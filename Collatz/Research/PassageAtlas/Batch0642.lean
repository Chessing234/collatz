import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0642

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21004. -/
theorem bounds_15_21004 : exactInterval 15 21004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21004 : oddCount 21004 15 = 4 ∧ acceleratedOrbit 15 21004 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21004) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21004.1, data_15_21004.2]

/-- Complete interval computation for depth 15, residue 21005. -/
theorem bounds_15_21005 : exactInterval 15 21005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21005 : oddCount 21005 15 = 4 ∧ acceleratedOrbit 15 21005 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21005) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21005.1, data_15_21005.2]

/-- Complete interval computation for depth 15, residue 21006. -/
theorem bounds_15_21006 : exactInterval 15 21006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21006 : oddCount 21006 15 = 8 ∧ acceleratedOrbit 15 21006 = 4207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21006) = 3 ^ 8 * m + 4207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21006.1, data_15_21006.2]

/-- Complete interval computation for depth 15, residue 21007. -/
theorem bounds_15_21007 : exactInterval 15 21007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21007 : oddCount 21007 15 = 8 ∧ acceleratedOrbit 15 21007 = 4207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21007) = 3 ^ 8 * m + 4207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21007.1, data_15_21007.2]

/-- Complete interval computation for depth 15, residue 21008. -/
theorem bounds_15_21008 : exactInterval 15 21008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21008 : oddCount 21008 15 = 4 ∧ acceleratedOrbit 15 21008 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21008) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21008.1, data_15_21008.2]

/-- Complete interval computation for depth 15, residue 21009. -/
theorem bounds_15_21009 : exactInterval 15 21009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21009 : oddCount 21009 15 = 4 ∧ acceleratedOrbit 15 21009 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21009) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21009.1, data_15_21009.2]

/-- Complete interval computation for depth 15, residue 21010. -/
theorem bounds_15_21010 : exactInterval 15 21010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21010 : oddCount 21010 15 = 7 ∧ acceleratedOrbit 15 21010 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21010) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21010.1, data_15_21010.2]

/-- Complete interval computation for depth 15, residue 21011. -/
theorem bounds_15_21011 : exactInterval 15 21011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21011 : oddCount 21011 15 = 7 ∧ acceleratedOrbit 15 21011 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21011) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21011.1, data_15_21011.2]

/-- Complete interval computation for depth 15, residue 21012. -/
theorem bounds_15_21012 : exactInterval 15 21012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21012 : oddCount 21012 15 = 4 ∧ acceleratedOrbit 15 21012 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21012) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21012.1, data_15_21012.2]

/-- Complete interval computation for depth 15, residue 21013. -/
theorem bounds_15_21013 : exactInterval 15 21013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21013 : oddCount 21013 15 = 4 ∧ acceleratedOrbit 15 21013 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21013) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21013.1, data_15_21013.2]

/-- Complete interval computation for depth 15, residue 21014. -/
theorem bounds_15_21014 : exactInterval 15 21014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21014 : oddCount 21014 15 = 8 ∧ acceleratedOrbit 15 21014 = 4211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21014) = 3 ^ 8 * m + 4211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21014.1, data_15_21014.2]

/-- Complete interval computation for depth 15, residue 21015. -/
theorem bounds_15_21015 : exactInterval 15 21015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21015 : oddCount 21015 15 = 8 ∧ acceleratedOrbit 15 21015 = 4211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21015) = 3 ^ 8 * m + 4211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21015.1, data_15_21015.2]

/-- Complete interval computation for depth 15, residue 21016. -/
theorem bounds_15_21016 : exactInterval 15 21016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21016 : oddCount 21016 15 = 4 ∧ acceleratedOrbit 15 21016 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21016) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21016.1, data_15_21016.2]

/-- Complete interval computation for depth 15, residue 21017. -/
theorem bounds_15_21017 : exactInterval 15 21017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21017 : oddCount 21017 15 = 8 ∧ acceleratedOrbit 15 21017 = 4211 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21017) = 3 ^ 8 * m + 4211 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21017.1, data_15_21017.2]

/-- Complete interval computation for depth 15, residue 21018. -/
theorem bounds_15_21018 : exactInterval 15 21018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21018 : oddCount 21018 15 = 4 ∧ acceleratedOrbit 15 21018 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21018) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21018.1, data_15_21018.2]

/-- Complete interval computation for depth 15, residue 21019. -/
theorem bounds_15_21019 : exactInterval 15 21019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21019 : oddCount 21019 15 = 11 ∧ acceleratedOrbit 15 21019 = 113642 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21019) = 3 ^ 11 * m + 113642 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21019.1, data_15_21019.2]

/-- Complete interval computation for depth 15, residue 21020. -/
theorem bounds_15_21020 : exactInterval 15 21020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21020 : oddCount 21020 15 = 9 ∧ acceleratedOrbit 15 21020 = 12635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21020) = 3 ^ 9 * m + 12635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21020.1, data_15_21020.2]

/-- Complete interval computation for depth 15, residue 21021. -/
theorem bounds_15_21021 : exactInterval 15 21021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21021 : oddCount 21021 15 = 9 ∧ acceleratedOrbit 15 21021 = 12635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21021) = 3 ^ 9 * m + 12635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21021.1, data_15_21021.2]

/-- Complete interval computation for depth 15, residue 21022. -/
theorem bounds_15_21022 : exactInterval 15 21022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21022 : oddCount 21022 15 = 9 ∧ acceleratedOrbit 15 21022 = 12635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21022) = 3 ^ 9 * m + 12635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21022.1, data_15_21022.2]

/-- Complete interval computation for depth 15, residue 21023. -/
theorem bounds_15_21023 : exactInterval 15 21023 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21023) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21023 : oddCount 21023 15 = 9 ∧ acceleratedOrbit 15 21023 = 12629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21023) = 3 ^ 9 * m + 12629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21023.1, data_15_21023.2]

/-- Complete interval computation for depth 15, residue 21024. -/
theorem bounds_15_21024 : exactInterval 15 21024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21024 : oddCount 21024 15 = 5 ∧ acceleratedOrbit 15 21024 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21024) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21024.1, data_15_21024.2]

/-- Complete interval computation for depth 15, residue 21025. -/
theorem bounds_15_21025 : exactInterval 15 21025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21025 : oddCount 21025 15 = 9 ∧ acceleratedOrbit 15 21025 = 12635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21025) = 3 ^ 9 * m + 12635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21025.1, data_15_21025.2]

/-- Complete interval computation for depth 15, residue 21026. -/
theorem bounds_15_21026 : exactInterval 15 21026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21026 : oddCount 21026 15 = 4 ∧ acceleratedOrbit 15 21026 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21026) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21026.1, data_15_21026.2]

/-- Complete interval computation for depth 15, residue 21027. -/
theorem bounds_15_21027 : exactInterval 15 21027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21027 : oddCount 21027 15 = 4 ∧ acceleratedOrbit 15 21027 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21027) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21027.1, data_15_21027.2]

/-- Complete interval computation for depth 15, residue 21028. -/
theorem bounds_15_21028 : exactInterval 15 21028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21028 : oddCount 21028 15 = 11 ∧ acceleratedOrbit 15 21028 = 113723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21028) = 3 ^ 11 * m + 113723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21028.1, data_15_21028.2]

/-- Complete interval computation for depth 15, residue 21029. -/
theorem bounds_15_21029 : exactInterval 15 21029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21029 : oddCount 21029 15 = 11 ∧ acceleratedOrbit 15 21029 = 113723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21029) = 3 ^ 11 * m + 113723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21029.1, data_15_21029.2]

/-- Complete interval computation for depth 15, residue 21030. -/
theorem bounds_15_21030 : exactInterval 15 21030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21030 : oddCount 21030 15 = 11 ∧ acceleratedOrbit 15 21030 = 113723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21030) = 3 ^ 11 * m + 113723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21030.1, data_15_21030.2]

/-- Complete interval computation for depth 15, residue 21031. -/
theorem bounds_15_21031 : exactInterval 15 21031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21031 : oddCount 21031 15 = 10 ∧ acceleratedOrbit 15 21031 = 37907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21031) = 3 ^ 10 * m + 37907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21031.1, data_15_21031.2]

/-- Complete interval computation for depth 15, residue 21032. -/
theorem bounds_15_21032 : exactInterval 15 21032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21032 : oddCount 21032 15 = 5 ∧ acceleratedOrbit 15 21032 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21032) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21032.1, data_15_21032.2]

/-- Complete interval computation for depth 15, residue 21033. -/
theorem bounds_15_21033 : exactInterval 15 21033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21033 : oddCount 21033 15 = 11 ∧ acceleratedOrbit 15 21033 = 113717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21033) = 3 ^ 11 * m + 113717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21033.1, data_15_21033.2]

/-- Complete interval computation for depth 15, residue 21034. -/
theorem bounds_15_21034 : exactInterval 15 21034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21034 : oddCount 21034 15 = 5 ∧ acceleratedOrbit 15 21034 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21034) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21034.1, data_15_21034.2]

/-- Complete interval computation for depth 15, residue 21035. -/
theorem bounds_15_21035 : exactInterval 15 21035 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21035 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21035) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21035 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21035 : oddCount 21035 15 = 4 ∧ acceleratedOrbit 15 21035 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21035 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21035) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21035.1, data_15_21035.2]

/-- Complete interval computation for depth 15, residue 21036. -/
theorem bounds_15_21036 : exactInterval 15 21036 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21036 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21036) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21036 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21036 : oddCount 21036 15 = 7 ∧ acceleratedOrbit 15 21036 = 1405 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21036 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21036) = 3 ^ 7 * m + 1405 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21036.1, data_15_21036.2]

end Collatz.Research.PassageAtlas.Batch0642
