import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0703

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23003. -/
theorem bounds_15_23003 : exactInterval 15 23003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23003 : oddCount 23003 15 = 8 ∧ acceleratedOrbit 15 23003 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23003) = 3 ^ 8 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23003.1, data_15_23003.2]

/-- Complete interval computation for depth 15, residue 23004. -/
theorem bounds_15_23004 : exactInterval 15 23004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23004 : oddCount 23004 15 = 7 ∧ acceleratedOrbit 15 23004 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23004) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23004.1, data_15_23004.2]

/-- Complete interval computation for depth 15, residue 23005. -/
theorem bounds_15_23005 : exactInterval 15 23005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23005 : oddCount 23005 15 = 7 ∧ acceleratedOrbit 15 23005 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23005) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23005.1, data_15_23005.2]

/-- Complete interval computation for depth 15, residue 23006. -/
theorem bounds_15_23006 : exactInterval 15 23006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23006 : oddCount 23006 15 = 12 ∧ acceleratedOrbit 15 23006 = 373157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23006) = 3 ^ 12 * m + 373157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23006.1, data_15_23006.2]

/-- Complete interval computation for depth 15, residue 23007. -/
theorem bounds_15_23007 : exactInterval 15 23007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23007 : oddCount 23007 15 = 12 ∧ acceleratedOrbit 15 23007 = 373157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23007) = 3 ^ 12 * m + 373157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23007.1, data_15_23007.2]

/-- Complete interval computation for depth 15, residue 23008. -/
theorem bounds_15_23008 : exactInterval 15 23008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23008 : oddCount 23008 15 = 8 ∧ acceleratedOrbit 15 23008 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23008) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23008.1, data_15_23008.2]

/-- Complete interval computation for depth 15, residue 23009. -/
theorem bounds_15_23009 : exactInterval 15 23009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23009 : oddCount 23009 15 = 10 ∧ acceleratedOrbit 15 23009 = 41471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23009) = 3 ^ 10 * m + 41471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23009.1, data_15_23009.2]

/-- Complete interval computation for depth 15, residue 23010. -/
theorem bounds_15_23010 : exactInterval 15 23010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23010 : oddCount 23010 15 = 8 ∧ acceleratedOrbit 15 23010 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23010) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23010.1, data_15_23010.2]

/-- Complete interval computation for depth 15, residue 23011. -/
theorem bounds_15_23011 : exactInterval 15 23011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23011 : oddCount 23011 15 = 8 ∧ acceleratedOrbit 15 23011 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23011) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23011.1, data_15_23011.2]

/-- Complete interval computation for depth 15, residue 23012. -/
theorem bounds_15_23012 : exactInterval 15 23012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23012 : oddCount 23012 15 = 8 ∧ acceleratedOrbit 15 23012 = 4610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23012) = 3 ^ 8 * m + 4610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23012.1, data_15_23012.2]

/-- Complete interval computation for depth 15, residue 23013. -/
theorem bounds_15_23013 : exactInterval 15 23013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23013 : oddCount 23013 15 = 8 ∧ acceleratedOrbit 15 23013 = 4610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23013) = 3 ^ 8 * m + 4610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23013.1, data_15_23013.2]

/-- Complete interval computation for depth 15, residue 23014. -/
theorem bounds_15_23014 : exactInterval 15 23014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23014 : oddCount 23014 15 = 8 ∧ acceleratedOrbit 15 23014 = 4610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23014) = 3 ^ 8 * m + 4610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23014.1, data_15_23014.2]

/-- Complete interval computation for depth 15, residue 23015. -/
theorem bounds_15_23015 : exactInterval 15 23015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23015 : oddCount 23015 15 = 9 ∧ acceleratedOrbit 15 23015 = 13826 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23015) = 3 ^ 9 * m + 13826 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23015.1, data_15_23015.2]

/-- Complete interval computation for depth 15, residue 23016. -/
theorem bounds_15_23016 : exactInterval 15 23016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23016 : oddCount 23016 15 = 8 ∧ acceleratedOrbit 15 23016 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23016) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23016.1, data_15_23016.2]

/-- Complete interval computation for depth 15, residue 23017. -/
theorem bounds_15_23017 : exactInterval 15 23017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23017 : oddCount 23017 15 = 8 ∧ acceleratedOrbit 15 23017 = 4609 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23017) = 3 ^ 8 * m + 4609 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23017.1, data_15_23017.2]

/-- Complete interval computation for depth 15, residue 23018. -/
theorem bounds_15_23018 : exactInterval 15 23018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23018 : oddCount 23018 15 = 8 ∧ acceleratedOrbit 15 23018 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23018) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23018.1, data_15_23018.2]

/-- Complete interval computation for depth 15, residue 23019. -/
theorem bounds_15_23019 : exactInterval 15 23019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23019 : oddCount 23019 15 = 10 ∧ acceleratedOrbit 15 23019 = 41485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23019) = 3 ^ 10 * m + 41485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23019.1, data_15_23019.2]

/-- Complete interval computation for depth 15, residue 23020. -/
theorem bounds_15_23020 : exactInterval 15 23020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23020 : oddCount 23020 15 = 7 ∧ acceleratedOrbit 15 23020 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23020) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23020.1, data_15_23020.2]

/-- Complete interval computation for depth 15, residue 23021. -/
theorem bounds_15_23021 : exactInterval 15 23021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23021 : oddCount 23021 15 = 7 ∧ acceleratedOrbit 15 23021 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23021) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23021.1, data_15_23021.2]

/-- Complete interval computation for depth 15, residue 23022. -/
theorem bounds_15_23022 : exactInterval 15 23022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23022 : oddCount 23022 15 = 7 ∧ acceleratedOrbit 15 23022 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23022) = 3 ^ 7 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23022.1, data_15_23022.2]

/-- Complete interval computation for depth 15, residue 23023. -/
theorem bounds_15_23023 : exactInterval 15 23023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23023 : oddCount 23023 15 = 11 ∧ acceleratedOrbit 15 23023 = 124472 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23023) = 3 ^ 11 * m + 124472 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23023.1, data_15_23023.2]

/-- Complete interval computation for depth 15, residue 23024. -/
theorem bounds_15_23024 : exactInterval 15 23024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23024 : oddCount 23024 15 = 9 ∧ acceleratedOrbit 15 23024 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23024) = 3 ^ 9 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23024.1, data_15_23024.2]

/-- Complete interval computation for depth 15, residue 23025. -/
theorem bounds_15_23025 : exactInterval 15 23025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23025 : oddCount 23025 15 = 8 ∧ acceleratedOrbit 15 23025 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23025) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23025.1, data_15_23025.2]

/-- Complete interval computation for depth 15, residue 23026. -/
theorem bounds_15_23026 : exactInterval 15 23026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23026 : oddCount 23026 15 = 8 ∧ acceleratedOrbit 15 23026 = 4612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23026) = 3 ^ 8 * m + 4612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23026.1, data_15_23026.2]

/-- Complete interval computation for depth 15, residue 23027. -/
theorem bounds_15_23027 : exactInterval 15 23027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23027 : oddCount 23027 15 = 8 ∧ acceleratedOrbit 15 23027 = 4612 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23027) = 3 ^ 8 * m + 4612 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23027.1, data_15_23027.2]

/-- Complete interval computation for depth 15, residue 23028. -/
theorem bounds_15_23028 : exactInterval 15 23028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23028 : oddCount 23028 15 = 9 ∧ acceleratedOrbit 15 23028 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23028) = 3 ^ 9 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23028.1, data_15_23028.2]

/-- Complete interval computation for depth 15, residue 23029. -/
theorem bounds_15_23029 : exactInterval 15 23029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23029 : oddCount 23029 15 = 9 ∧ acceleratedOrbit 15 23029 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23029) = 3 ^ 9 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23029.1, data_15_23029.2]

/-- Complete interval computation for depth 15, residue 23030. -/
theorem bounds_15_23030 : exactInterval 15 23030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23030 : oddCount 23030 15 = 11 ∧ acceleratedOrbit 15 23030 = 124523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23030) = 3 ^ 11 * m + 124523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23030.1, data_15_23030.2]

/-- Complete interval computation for depth 15, residue 23031. -/
theorem bounds_15_23031 : exactInterval 15 23031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23031 : oddCount 23031 15 = 11 ∧ acceleratedOrbit 15 23031 = 124523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23031) = 3 ^ 11 * m + 124523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23031.1, data_15_23031.2]

/-- Complete interval computation for depth 15, residue 23032. -/
theorem bounds_15_23032 : exactInterval 15 23032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23032 : oddCount 23032 15 = 9 ∧ acceleratedOrbit 15 23032 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23032) = 3 ^ 9 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23032.1, data_15_23032.2]

/-- Complete interval computation for depth 15, residue 23033. -/
theorem bounds_15_23033 : exactInterval 15 23033 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23033 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23033) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23033 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23033 : oddCount 23033 15 = 10 ∧ acceleratedOrbit 15 23033 = 41512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23033 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23033) = 3 ^ 10 * m + 41512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23033.1, data_15_23033.2]

/-- Complete interval computation for depth 15, residue 23034. -/
theorem bounds_15_23034 : exactInterval 15 23034 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23034 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23034) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23034 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23034 : oddCount 23034 15 = 9 ∧ acceleratedOrbit 15 23034 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23034 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23034) = 3 ^ 9 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23034.1, data_15_23034.2]

end Collatz.Research.PassageAtlas.Batch0703
