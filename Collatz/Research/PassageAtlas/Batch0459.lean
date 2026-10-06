import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0459

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15007. -/
theorem bounds_15_15007 : exactInterval 15 15007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15007 : oddCount 15007 15 = 8 ∧ acceleratedOrbit 15 15007 = 3005 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15007) = 3 ^ 8 * m + 3005 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15007.1, data_15_15007.2]

/-- Complete interval computation for depth 15, residue 15008. -/
theorem bounds_15_15008 : exactInterval 15 15008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15008 : oddCount 15008 15 = 3 ∧ acceleratedOrbit 15 15008 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15008) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15008.1, data_15_15008.2]

/-- Complete interval computation for depth 15, residue 15009. -/
theorem bounds_15_15009 : exactInterval 15 15009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15009 : oddCount 15009 15 = 11 ∧ acceleratedOrbit 15 15009 = 81161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15009) = 3 ^ 11 * m + 81161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15009.1, data_15_15009.2]

/-- Complete interval computation for depth 15, residue 15010. -/
theorem bounds_15_15010 : exactInterval 15 15010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15010 : oddCount 15010 15 = 8 ∧ acceleratedOrbit 15 15010 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15010) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15010.1, data_15_15010.2]

/-- Complete interval computation for depth 15, residue 15011. -/
theorem bounds_15_15011 : exactInterval 15 15011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15011 : oddCount 15011 15 = 8 ∧ acceleratedOrbit 15 15011 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15011) = 3 ^ 8 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15011.1, data_15_15011.2]

/-- Complete interval computation for depth 15, residue 15012. -/
theorem bounds_15_15012 : exactInterval 15 15012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15012 : oddCount 15012 15 = 10 ∧ acceleratedOrbit 15 15012 = 27064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15012) = 3 ^ 10 * m + 27064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15012.1, data_15_15012.2]

/-- Complete interval computation for depth 15, residue 15013. -/
theorem bounds_15_15013 : exactInterval 15 15013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15013 : oddCount 15013 15 = 10 ∧ acceleratedOrbit 15 15013 = 27064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15013) = 3 ^ 10 * m + 27064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15013.1, data_15_15013.2]

/-- Complete interval computation for depth 15, residue 15014. -/
theorem bounds_15_15014 : exactInterval 15 15014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15014 : oddCount 15014 15 = 10 ∧ acceleratedOrbit 15 15014 = 27064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15014) = 3 ^ 10 * m + 27064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15014.1, data_15_15014.2]

/-- Complete interval computation for depth 15, residue 15015. -/
theorem bounds_15_15015 : exactInterval 15 15015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15015 : oddCount 15015 15 = 11 ∧ acceleratedOrbit 15 15015 = 81182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15015) = 3 ^ 11 * m + 81182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15015.1, data_15_15015.2]

/-- Complete interval computation for depth 15, residue 15016. -/
theorem bounds_15_15016 : exactInterval 15 15016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15016 : oddCount 15016 15 = 3 ∧ acceleratedOrbit 15 15016 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15016) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15016.1, data_15_15016.2]

/-- Complete interval computation for depth 15, residue 15017. -/
theorem bounds_15_15017 : exactInterval 15 15017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15017 : oddCount 15017 15 = 12 ∧ acceleratedOrbit 15 15017 = 243577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15017) = 3 ^ 12 * m + 243577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15017.1, data_15_15017.2]

/-- Complete interval computation for depth 15, residue 15018. -/
theorem bounds_15_15018 : exactInterval 15 15018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15018 : oddCount 15018 15 = 3 ∧ acceleratedOrbit 15 15018 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15018) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15018.1, data_15_15018.2]

/-- Complete interval computation for depth 15, residue 15019. -/
theorem bounds_15_15019 : exactInterval 15 15019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15019 : oddCount 15019 15 = 8 ∧ acceleratedOrbit 15 15019 = 3008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15019) = 3 ^ 8 * m + 3008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15019.1, data_15_15019.2]

/-- Complete interval computation for depth 15, residue 15020. -/
theorem bounds_15_15020 : exactInterval 15 15020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15020 : oddCount 15020 15 = 8 ∧ acceleratedOrbit 15 15020 = 3010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15020) = 3 ^ 8 * m + 3010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15020.1, data_15_15020.2]

/-- Complete interval computation for depth 15, residue 15021. -/
theorem bounds_15_15021 : exactInterval 15 15021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15021 : oddCount 15021 15 = 8 ∧ acceleratedOrbit 15 15021 = 3010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15021) = 3 ^ 8 * m + 3010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15021.1, data_15_15021.2]

/-- Complete interval computation for depth 15, residue 15022. -/
theorem bounds_15_15022 : exactInterval 15 15022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15022 : oddCount 15022 15 = 8 ∧ acceleratedOrbit 15 15022 = 3010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15022) = 3 ^ 8 * m + 3010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15022.1, data_15_15022.2]

/-- Complete interval computation for depth 15, residue 15023. -/
theorem bounds_15_15023 : exactInterval 15 15023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15023 : oddCount 15023 15 = 7 ∧ acceleratedOrbit 15 15023 = 1003 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15023) = 3 ^ 7 * m + 1003 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15023.1, data_15_15023.2]

/-- Complete interval computation for depth 15, residue 15024. -/
theorem bounds_15_15024 : exactInterval 15 15024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15024 : oddCount 15024 15 = 6 ∧ acceleratedOrbit 15 15024 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15024) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15024.1, data_15_15024.2]

/-- Complete interval computation for depth 15, residue 15025. -/
theorem bounds_15_15025 : exactInterval 15 15025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15025 : oddCount 15025 15 = 6 ∧ acceleratedOrbit 15 15025 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15025) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15025.1, data_15_15025.2]

/-- Complete interval computation for depth 15, residue 15026. -/
theorem bounds_15_15026 : exactInterval 15 15026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15026 : oddCount 15026 15 = 6 ∧ acceleratedOrbit 15 15026 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15026) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15026.1, data_15_15026.2]

/-- Complete interval computation for depth 15, residue 15027. -/
theorem bounds_15_15027 : exactInterval 15 15027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15027 : oddCount 15027 15 = 6 ∧ acceleratedOrbit 15 15027 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15027) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15027.1, data_15_15027.2]

/-- Complete interval computation for depth 15, residue 15028. -/
theorem bounds_15_15028 : exactInterval 15 15028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15028 : oddCount 15028 15 = 6 ∧ acceleratedOrbit 15 15028 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15028) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15028.1, data_15_15028.2]

/-- Complete interval computation for depth 15, residue 15029. -/
theorem bounds_15_15029 : exactInterval 15 15029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15029 : oddCount 15029 15 = 6 ∧ acceleratedOrbit 15 15029 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15029) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15029.1, data_15_15029.2]

/-- Complete interval computation for depth 15, residue 15030. -/
theorem bounds_15_15030 : exactInterval 15 15030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15030 : oddCount 15030 15 = 9 ∧ acceleratedOrbit 15 15030 = 9031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15030) = 3 ^ 9 * m + 9031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15030.1, data_15_15030.2]

/-- Complete interval computation for depth 15, residue 15031. -/
theorem bounds_15_15031 : exactInterval 15 15031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15031 : oddCount 15031 15 = 9 ∧ acceleratedOrbit 15 15031 = 9031 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15031) = 3 ^ 9 * m + 9031 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15031.1, data_15_15031.2]

/-- Complete interval computation for depth 15, residue 15032. -/
theorem bounds_15_15032 : exactInterval 15 15032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15032 : oddCount 15032 15 = 6 ∧ acceleratedOrbit 15 15032 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15032) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15032.1, data_15_15032.2]

/-- Complete interval computation for depth 15, residue 15033. -/
theorem bounds_15_15033 : exactInterval 15 15033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15033 : oddCount 15033 15 = 6 ∧ acceleratedOrbit 15 15033 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15033) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15033.1, data_15_15033.2]

/-- Complete interval computation for depth 15, residue 15034. -/
theorem bounds_15_15034 : exactInterval 15 15034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15034 : oddCount 15034 15 = 6 ∧ acceleratedOrbit 15 15034 = 335 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15034) = 3 ^ 6 * m + 335 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15034.1, data_15_15034.2]

/-- Complete interval computation for depth 15, residue 15035. -/
theorem bounds_15_15035 : exactInterval 15 15035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15035 : oddCount 15035 15 = 8 ∧ acceleratedOrbit 15 15035 = 3011 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15035) = 3 ^ 8 * m + 3011 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15035.1, data_15_15035.2]

/-- Complete interval computation for depth 15, residue 15036. -/
theorem bounds_15_15036 : exactInterval 15 15036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15036 : oddCount 15036 15 = 7 ∧ acceleratedOrbit 15 15036 = 1004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15036) = 3 ^ 7 * m + 1004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15036.1, data_15_15036.2]

/-- Complete interval computation for depth 15, residue 15037. -/
theorem bounds_15_15037 : exactInterval 15 15037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15037 : oddCount 15037 15 = 7 ∧ acceleratedOrbit 15 15037 = 1004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15037) = 3 ^ 7 * m + 1004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15037.1, data_15_15037.2]

/-- Complete interval computation for depth 15, residue 15038. -/
theorem bounds_15_15038 : exactInterval 15 15038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15038 : oddCount 15038 15 = 7 ∧ acceleratedOrbit 15 15038 = 1004 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15038) = 3 ^ 7 * m + 1004 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15038.1, data_15_15038.2]

/-- Complete interval computation for depth 15, residue 15039. -/
theorem bounds_15_15039 : exactInterval 15 15039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15039 : oddCount 15039 15 = 10 ∧ acceleratedOrbit 15 15039 = 27103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15039) = 3 ^ 10 * m + 27103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15039.1, data_15_15039.2]

end Collatz.Research.PassageAtlas.Batch0459
