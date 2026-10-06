import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0397

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3010. -/
theorem bounds_12_3010 : exactInterval 12 3010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3010 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3010) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3010 : oddCount 3010 12 = 7 ∧ acceleratedOrbit 12 3010 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3010 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3010) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3010.1, data_12_3010.2]

/-- Complete interval computation for depth 12, residue 3011. -/
theorem bounds_12_3011 : exactInterval 12 3011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3011 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3011) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3011 : oddCount 3011 12 = 7 ∧ acceleratedOrbit 12 3011 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3011 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3011) = 3 ^ 7 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3011.1, data_12_3011.2]

/-- Complete interval computation for depth 12, residue 3012. -/
theorem bounds_12_3012 : exactInterval 12 3012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3012 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3012) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3012 : oddCount 3012 12 = 3 ∧ acceleratedOrbit 12 3012 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3012 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3012) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3012.1, data_12_3012.2]

/-- Complete interval computation for depth 12, residue 3013. -/
theorem bounds_12_3013 : exactInterval 12 3013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3013 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3013) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3013 : oddCount 3013 12 = 3 ∧ acceleratedOrbit 12 3013 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3013 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3013) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3013.1, data_12_3013.2]

/-- Complete interval computation for depth 12, residue 3014. -/
theorem bounds_12_3014 : exactInterval 12 3014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3014 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3014) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3014 : oddCount 3014 12 = 3 ∧ acceleratedOrbit 12 3014 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3014 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3014) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3014.1, data_12_3014.2]

/-- Complete interval computation for depth 12, residue 3015. -/
theorem bounds_12_3015 : exactInterval 12 3015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3015 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3015) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3015 : oddCount 3015 12 = 9 ∧ acceleratedOrbit 12 3015 = 14498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3015 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3015) = 3 ^ 9 * m + 14498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3015.1, data_12_3015.2]

/-- Complete interval computation for depth 12, residue 3016. -/
theorem bounds_12_3016 : exactInterval 12 3016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3016 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3016) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3016 : oddCount 3016 12 = 7 ∧ acceleratedOrbit 12 3016 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3016 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3016) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3016.1, data_12_3016.2]

/-- Complete interval computation for depth 12, residue 3017. -/
theorem bounds_12_3017 : exactInterval 12 3017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3017 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3017) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3017 : oddCount 3017 12 = 7 ∧ acceleratedOrbit 12 3017 = 1613 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3017 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3017) = 3 ^ 7 * m + 1613 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3017.1, data_12_3017.2]

/-- Complete interval computation for depth 12, residue 3018. -/
theorem bounds_12_3018 : exactInterval 12 3018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3018 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3018) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3018 : oddCount 3018 12 = 7 ∧ acceleratedOrbit 12 3018 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3018 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3018) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3018.1, data_12_3018.2]

/-- Complete interval computation for depth 12, residue 3019. -/
theorem bounds_12_3019 : exactInterval 12 3019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3019 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3019) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3019 : oddCount 3019 12 = 6 ∧ acceleratedOrbit 12 3019 = 539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3019 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3019) = 3 ^ 6 * m + 539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3019.1, data_12_3019.2]

/-- Complete interval computation for depth 12, residue 3020. -/
theorem bounds_12_3020 : exactInterval 12 3020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3020 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3020) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3020 : oddCount 3020 12 = 7 ∧ acceleratedOrbit 12 3020 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3020 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3020) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3020.1, data_12_3020.2]

/-- Complete interval computation for depth 12, residue 3021. -/
theorem bounds_12_3021 : exactInterval 12 3021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3021 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3021) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3021 : oddCount 3021 12 = 7 ∧ acceleratedOrbit 12 3021 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3021 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3021) = 3 ^ 7 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3021.1, data_12_3021.2]

/-- Complete interval computation for depth 12, residue 3022. -/
theorem bounds_12_3022 : exactInterval 12 3022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3022 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3022) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3022 : oddCount 3022 12 = 7 ∧ acceleratedOrbit 12 3022 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3022 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3022) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3022.1, data_12_3022.2]

/-- Complete interval computation for depth 12, residue 3023. -/
theorem bounds_12_3023 : exactInterval 12 3023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3023 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3023) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3023 : oddCount 3023 12 = 7 ∧ acceleratedOrbit 12 3023 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3023 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3023) = 3 ^ 7 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3023.1, data_12_3023.2]

/-- Complete interval computation for depth 12, residue 3024. -/
theorem bounds_12_3024 : exactInterval 12 3024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3024 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3024) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3024 : oddCount 3024 12 = 5 ∧ acceleratedOrbit 12 3024 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3024 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3024) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3024.1, data_12_3024.2]

end Collatz.Research.StoppingAtlas.Batch0397
