import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0581

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19005. -/
theorem bounds_15_19005 : exactInterval 15 19005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19005 : oddCount 19005 15 = 10 ∧ acceleratedOrbit 15 19005 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19005) = 3 ^ 10 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19005.1, data_15_19005.2]

/-- Complete interval computation for depth 15, residue 19006. -/
theorem bounds_15_19006 : exactInterval 15 19006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19006 : oddCount 19006 15 = 9 ∧ acceleratedOrbit 15 19006 = 11420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19006) = 3 ^ 9 * m + 11420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19006.1, data_15_19006.2]

/-- Complete interval computation for depth 15, residue 19007. -/
theorem bounds_15_19007 : exactInterval 15 19007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19007 : oddCount 19007 15 = 9 ∧ acceleratedOrbit 15 19007 = 11420 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19007) = 3 ^ 9 * m + 11420 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19007.1, data_15_19007.2]

/-- Complete interval computation for depth 15, residue 19008. -/
theorem bounds_15_19008 : exactInterval 15 19008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19008 : oddCount 19008 15 = 6 ∧ acceleratedOrbit 15 19008 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19008) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19008.1, data_15_19008.2]

/-- Complete interval computation for depth 15, residue 19009. -/
theorem bounds_15_19009 : exactInterval 15 19009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19009 : oddCount 19009 15 = 4 ∧ acceleratedOrbit 15 19009 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19009) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19009.1, data_15_19009.2]

/-- Complete interval computation for depth 15, residue 19010. -/
theorem bounds_15_19010 : exactInterval 15 19010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19010 : oddCount 19010 15 = 4 ∧ acceleratedOrbit 15 19010 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19010) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19010.1, data_15_19010.2]

/-- Complete interval computation for depth 15, residue 19011. -/
theorem bounds_15_19011 : exactInterval 15 19011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19011 : oddCount 19011 15 = 4 ∧ acceleratedOrbit 15 19011 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19011) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19011.1, data_15_19011.2]

/-- Complete interval computation for depth 15, residue 19012. -/
theorem bounds_15_19012 : exactInterval 15 19012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19012 : oddCount 19012 15 = 7 ∧ acceleratedOrbit 15 19012 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19012) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19012.1, data_15_19012.2]

/-- Complete interval computation for depth 15, residue 19013. -/
theorem bounds_15_19013 : exactInterval 15 19013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19013 : oddCount 19013 15 = 7 ∧ acceleratedOrbit 15 19013 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19013) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19013.1, data_15_19013.2]

/-- Complete interval computation for depth 15, residue 19014. -/
theorem bounds_15_19014 : exactInterval 15 19014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19014 : oddCount 19014 15 = 7 ∧ acceleratedOrbit 15 19014 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19014) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19014.1, data_15_19014.2]

/-- Complete interval computation for depth 15, residue 19015. -/
theorem bounds_15_19015 : exactInterval 15 19015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19015 : oddCount 19015 15 = 8 ∧ acceleratedOrbit 15 19015 = 3808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19015) = 3 ^ 8 * m + 3808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19015.1, data_15_19015.2]

/-- Complete interval computation for depth 15, residue 19016. -/
theorem bounds_15_19016 : exactInterval 15 19016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19016 : oddCount 19016 15 = 7 ∧ acceleratedOrbit 15 19016 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19016) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19016.1, data_15_19016.2]

/-- Complete interval computation for depth 15, residue 19017. -/
theorem bounds_15_19017 : exactInterval 15 19017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19017 : oddCount 19017 15 = 8 ∧ acceleratedOrbit 15 19017 = 3809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19017) = 3 ^ 8 * m + 3809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19017.1, data_15_19017.2]

/-- Complete interval computation for depth 15, residue 19018. -/
theorem bounds_15_19018 : exactInterval 15 19018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19018 : oddCount 19018 15 = 7 ∧ acceleratedOrbit 15 19018 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19018) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19018.1, data_15_19018.2]

/-- Complete interval computation for depth 15, residue 19019. -/
theorem bounds_15_19019 : exactInterval 15 19019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19019 : oddCount 19019 15 = 7 ∧ acceleratedOrbit 15 19019 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19019) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19019.1, data_15_19019.2]

/-- Complete interval computation for depth 15, residue 19020. -/
theorem bounds_15_19020 : exactInterval 15 19020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19020 : oddCount 19020 15 = 7 ∧ acceleratedOrbit 15 19020 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19020) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19020.1, data_15_19020.2]

/-- Complete interval computation for depth 15, residue 19021. -/
theorem bounds_15_19021 : exactInterval 15 19021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19021 : oddCount 19021 15 = 7 ∧ acceleratedOrbit 15 19021 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19021) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19021.1, data_15_19021.2]

/-- Complete interval computation for depth 15, residue 19022. -/
theorem bounds_15_19022 : exactInterval 15 19022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19022 : oddCount 19022 15 = 7 ∧ acceleratedOrbit 15 19022 = 1270 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19022) = 3 ^ 7 * m + 1270 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19022.1, data_15_19022.2]

/-- Complete interval computation for depth 15, residue 19023. -/
theorem bounds_15_19023 : exactInterval 15 19023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19023 : oddCount 19023 15 = 7 ∧ acceleratedOrbit 15 19023 = 1270 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19023) = 3 ^ 7 * m + 1270 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19023.1, data_15_19023.2]

/-- Complete interval computation for depth 15, residue 19024. -/
theorem bounds_15_19024 : exactInterval 15 19024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19024 : oddCount 19024 15 = 6 ∧ acceleratedOrbit 15 19024 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19024) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19024.1, data_15_19024.2]

/-- Complete interval computation for depth 15, residue 19025. -/
theorem bounds_15_19025 : exactInterval 15 19025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19025 : oddCount 19025 15 = 9 ∧ acceleratedOrbit 15 19025 = 11431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19025) = 3 ^ 9 * m + 11431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19025.1, data_15_19025.2]

/-- Complete interval computation for depth 15, residue 19026. -/
theorem bounds_15_19026 : exactInterval 15 19026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19026 : oddCount 19026 15 = 9 ∧ acceleratedOrbit 15 19026 = 11431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19026) = 3 ^ 9 * m + 11431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19026.1, data_15_19026.2]

/-- Complete interval computation for depth 15, residue 19027. -/
theorem bounds_15_19027 : exactInterval 15 19027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19027 : oddCount 19027 15 = 9 ∧ acceleratedOrbit 15 19027 = 11431 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19027) = 3 ^ 9 * m + 11431 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19027.1, data_15_19027.2]

/-- Complete interval computation for depth 15, residue 19028. -/
theorem bounds_15_19028 : exactInterval 15 19028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19028 : oddCount 19028 15 = 6 ∧ acceleratedOrbit 15 19028 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19028) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19028.1, data_15_19028.2]

/-- Complete interval computation for depth 15, residue 19029. -/
theorem bounds_15_19029 : exactInterval 15 19029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19029 : oddCount 19029 15 = 6 ∧ acceleratedOrbit 15 19029 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19029) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19029.1, data_15_19029.2]

/-- Complete interval computation for depth 15, residue 19030. -/
theorem bounds_15_19030 : exactInterval 15 19030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19030 : oddCount 19030 15 = 7 ∧ acceleratedOrbit 15 19030 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19030) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19030.1, data_15_19030.2]

/-- Complete interval computation for depth 15, residue 19031. -/
theorem bounds_15_19031 : exactInterval 15 19031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19031 : oddCount 19031 15 = 7 ∧ acceleratedOrbit 15 19031 = 1271 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19031) = 3 ^ 7 * m + 1271 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19031.1, data_15_19031.2]

/-- Complete interval computation for depth 15, residue 19032. -/
theorem bounds_15_19032 : exactInterval 15 19032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19032 : oddCount 19032 15 = 6 ∧ acceleratedOrbit 15 19032 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19032) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19032.1, data_15_19032.2]

/-- Complete interval computation for depth 15, residue 19033. -/
theorem bounds_15_19033 : exactInterval 15 19033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19033 : oddCount 19033 15 = 8 ∧ acceleratedOrbit 15 19033 = 3812 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19033) = 3 ^ 8 * m + 3812 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19033.1, data_15_19033.2]

/-- Complete interval computation for depth 15, residue 19034. -/
theorem bounds_15_19034 : exactInterval 15 19034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19034 : oddCount 19034 15 = 6 ∧ acceleratedOrbit 15 19034 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19034) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19034.1, data_15_19034.2]

/-- Complete interval computation for depth 15, residue 19035. -/
theorem bounds_15_19035 : exactInterval 15 19035 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19035) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19035 : oddCount 19035 15 = 9 ∧ acceleratedOrbit 15 19035 = 11435 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19035) = 3 ^ 9 * m + 11435 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19035.1, data_15_19035.2]

/-- Complete interval computation for depth 15, residue 19036. -/
theorem bounds_15_19036 : exactInterval 15 19036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19036 : oddCount 19036 15 = 6 ∧ acceleratedOrbit 15 19036 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19036) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19036.1, data_15_19036.2]

/-- Complete interval computation for depth 15, residue 19037. -/
theorem bounds_15_19037 : exactInterval 15 19037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19037 : oddCount 19037 15 = 6 ∧ acceleratedOrbit 15 19037 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19037) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19037.1, data_15_19037.2]

end Collatz.Research.PassageAtlas.Batch0581
