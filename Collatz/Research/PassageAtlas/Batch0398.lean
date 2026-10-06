import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0398

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13008. -/
theorem bounds_15_13008 : exactInterval 15 13008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13008 : oddCount 13008 15 = 5 ∧ acceleratedOrbit 15 13008 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13008) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13008.1, data_15_13008.2]

/-- Complete interval computation for depth 15, residue 13009. -/
theorem bounds_15_13009 : exactInterval 15 13009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13009 : oddCount 13009 15 = 6 ∧ acceleratedOrbit 15 13009 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13009) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13009.1, data_15_13009.2]

/-- Complete interval computation for depth 15, residue 13010. -/
theorem bounds_15_13010 : exactInterval 15 13010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13010 : oddCount 13010 15 = 6 ∧ acceleratedOrbit 15 13010 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13010) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13010.1, data_15_13010.2]

/-- Complete interval computation for depth 15, residue 13011. -/
theorem bounds_15_13011 : exactInterval 15 13011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13011 : oddCount 13011 15 = 6 ∧ acceleratedOrbit 15 13011 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13011) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13011.1, data_15_13011.2]

/-- Complete interval computation for depth 15, residue 13012. -/
theorem bounds_15_13012 : exactInterval 15 13012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13012 : oddCount 13012 15 = 5 ∧ acceleratedOrbit 15 13012 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13012) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13012.1, data_15_13012.2]

/-- Complete interval computation for depth 15, residue 13013. -/
theorem bounds_15_13013 : exactInterval 15 13013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13013 : oddCount 13013 15 = 5 ∧ acceleratedOrbit 15 13013 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13013) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13013.1, data_15_13013.2]

/-- Complete interval computation for depth 15, residue 13014. -/
theorem bounds_15_13014 : exactInterval 15 13014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13014 : oddCount 13014 15 = 7 ∧ acceleratedOrbit 15 13014 = 869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13014) = 3 ^ 7 * m + 869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13014.1, data_15_13014.2]

/-- Complete interval computation for depth 15, residue 13015. -/
theorem bounds_15_13015 : exactInterval 15 13015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13015 : oddCount 13015 15 = 7 ∧ acceleratedOrbit 15 13015 = 869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13015) = 3 ^ 7 * m + 869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13015.1, data_15_13015.2]

/-- Complete interval computation for depth 15, residue 13016. -/
theorem bounds_15_13016 : exactInterval 15 13016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13016 : oddCount 13016 15 = 8 ∧ acceleratedOrbit 15 13016 = 2609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13016) = 3 ^ 8 * m + 2609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13016.1, data_15_13016.2]

/-- Complete interval computation for depth 15, residue 13017. -/
theorem bounds_15_13017 : exactInterval 15 13017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13017 : oddCount 13017 15 = 6 ∧ acceleratedOrbit 15 13017 = 290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13017) = 3 ^ 6 * m + 290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13017.1, data_15_13017.2]

/-- Complete interval computation for depth 15, residue 13018. -/
theorem bounds_15_13018 : exactInterval 15 13018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13018 : oddCount 13018 15 = 8 ∧ acceleratedOrbit 15 13018 = 2609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13018) = 3 ^ 8 * m + 2609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13018.1, data_15_13018.2]

/-- Complete interval computation for depth 15, residue 13019. -/
theorem bounds_15_13019 : exactInterval 15 13019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13019 : oddCount 13019 15 = 10 ∧ acceleratedOrbit 15 13019 = 23465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13019) = 3 ^ 10 * m + 23465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13019.1, data_15_13019.2]

/-- Complete interval computation for depth 15, residue 13020. -/
theorem bounds_15_13020 : exactInterval 15 13020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13020 : oddCount 13020 15 = 8 ∧ acceleratedOrbit 15 13020 = 2609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13020) = 3 ^ 8 * m + 2609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13020.1, data_15_13020.2]

/-- Complete interval computation for depth 15, residue 13021. -/
theorem bounds_15_13021 : exactInterval 15 13021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13021 : oddCount 13021 15 = 8 ∧ acceleratedOrbit 15 13021 = 2609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13021) = 3 ^ 8 * m + 2609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13021.1, data_15_13021.2]

/-- Complete interval computation for depth 15, residue 13022. -/
theorem bounds_15_13022 : exactInterval 15 13022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13022 : oddCount 13022 15 = 8 ∧ acceleratedOrbit 15 13022 = 2609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13022) = 3 ^ 8 * m + 2609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13022.1, data_15_13022.2]

/-- Complete interval computation for depth 15, residue 13023. -/
theorem bounds_15_13023 : exactInterval 15 13023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13023 : oddCount 13023 15 = 8 ∧ acceleratedOrbit 15 13023 = 2609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13023) = 3 ^ 8 * m + 2609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13023.1, data_15_13023.2]

/-- Complete interval computation for depth 15, residue 13024. -/
theorem bounds_15_13024 : exactInterval 15 13024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13024 : oddCount 13024 15 = 5 ∧ acceleratedOrbit 15 13024 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13024) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13024.1, data_15_13024.2]

/-- Complete interval computation for depth 15, residue 13025. -/
theorem bounds_15_13025 : exactInterval 15 13025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13025 : oddCount 13025 15 = 11 ∧ acceleratedOrbit 15 13025 = 70429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13025) = 3 ^ 11 * m + 70429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13025.1, data_15_13025.2]

/-- Complete interval computation for depth 15, residue 13026. -/
theorem bounds_15_13026 : exactInterval 15 13026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13026 : oddCount 13026 15 = 5 ∧ acceleratedOrbit 15 13026 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13026) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13026.1, data_15_13026.2]

/-- Complete interval computation for depth 15, residue 13027. -/
theorem bounds_15_13027 : exactInterval 15 13027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13027 : oddCount 13027 15 = 5 ∧ acceleratedOrbit 15 13027 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13027) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13027.1, data_15_13027.2]

/-- Complete interval computation for depth 15, residue 13028. -/
theorem bounds_15_13028 : exactInterval 15 13028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13028 : oddCount 13028 15 = 8 ∧ acceleratedOrbit 15 13028 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13028) = 3 ^ 8 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13028.1, data_15_13028.2]

/-- Complete interval computation for depth 15, residue 13029. -/
theorem bounds_15_13029 : exactInterval 15 13029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13029 : oddCount 13029 15 = 8 ∧ acceleratedOrbit 15 13029 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13029) = 3 ^ 8 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13029.1, data_15_13029.2]

/-- Complete interval computation for depth 15, residue 13030. -/
theorem bounds_15_13030 : exactInterval 15 13030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13030 : oddCount 13030 15 = 8 ∧ acceleratedOrbit 15 13030 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13030) = 3 ^ 8 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13030.1, data_15_13030.2]

/-- Complete interval computation for depth 15, residue 13031. -/
theorem bounds_15_13031 : exactInterval 15 13031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13031 : oddCount 13031 15 = 10 ∧ acceleratedOrbit 15 13031 = 23485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13031) = 3 ^ 10 * m + 23485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13031.1, data_15_13031.2]

/-- Complete interval computation for depth 15, residue 13032. -/
theorem bounds_15_13032 : exactInterval 15 13032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13032 : oddCount 13032 15 = 5 ∧ acceleratedOrbit 15 13032 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13032) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13032.1, data_15_13032.2]

/-- Complete interval computation for depth 15, residue 13033. -/
theorem bounds_15_13033 : exactInterval 15 13033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13033 : oddCount 13033 15 = 12 ∧ acceleratedOrbit 15 13033 = 211409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13033) = 3 ^ 12 * m + 211409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13033.1, data_15_13033.2]

/-- Complete interval computation for depth 15, residue 13034. -/
theorem bounds_15_13034 : exactInterval 15 13034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13034 : oddCount 13034 15 = 5 ∧ acceleratedOrbit 15 13034 = 98 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13034) = 3 ^ 5 * m + 98 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13034.1, data_15_13034.2]

/-- Complete interval computation for depth 15, residue 13035. -/
theorem bounds_15_13035 : exactInterval 15 13035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13035 : oddCount 13035 15 = 9 ∧ acceleratedOrbit 15 13035 = 7832 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13035) = 3 ^ 9 * m + 7832 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13035.1, data_15_13035.2]

/-- Complete interval computation for depth 15, residue 13036. -/
theorem bounds_15_13036 : exactInterval 15 13036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13036 : oddCount 13036 15 = 8 ∧ acceleratedOrbit 15 13036 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13036) = 3 ^ 8 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13036.1, data_15_13036.2]

/-- Complete interval computation for depth 15, residue 13037. -/
theorem bounds_15_13037 : exactInterval 15 13037 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13037 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13037) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13037 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13037 : oddCount 13037 15 = 8 ∧ acceleratedOrbit 15 13037 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13037 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13037) = 3 ^ 8 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13037.1, data_15_13037.2]

/-- Complete interval computation for depth 15, residue 13038. -/
theorem bounds_15_13038 : exactInterval 15 13038 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13038 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13038) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13038 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13038 : oddCount 13038 15 = 8 ∧ acceleratedOrbit 15 13038 = 2612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13038 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13038) = 3 ^ 8 * m + 2612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13038.1, data_15_13038.2]

/-- Complete interval computation for depth 15, residue 13039. -/
theorem bounds_15_13039 : exactInterval 15 13039 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13039 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13039) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13039 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13039 : oddCount 13039 15 = 13 ∧ acceleratedOrbit 15 13039 = 634472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13039 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13039) = 3 ^ 13 * m + 634472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13039.1, data_15_13039.2]

/-- Complete interval computation for depth 15, residue 13040. -/
theorem bounds_15_13040 : exactInterval 15 13040 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13040 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13040) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13040 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13040 : oddCount 13040 15 = 7 ∧ acceleratedOrbit 15 13040 = 872 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13040 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13040) = 3 ^ 7 * m + 872 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13040.1, data_15_13040.2]

end Collatz.Research.PassageAtlas.Batch0398
