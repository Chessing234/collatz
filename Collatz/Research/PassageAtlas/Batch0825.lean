import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0825

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27000. -/
theorem bounds_15_27000 : exactInterval 15 27000 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27000 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27000) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27000 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27000 : oddCount 27000 15 = 9 ∧ acceleratedOrbit 15 27000 = 16226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27000 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27000) = 3 ^ 9 * m + 16226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27000.1, data_15_27000.2]

/-- Complete interval computation for depth 15, residue 27001. -/
theorem bounds_15_27001 : exactInterval 15 27001 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27001 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27001) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27001 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27001 : oddCount 27001 15 = 11 ∧ acceleratedOrbit 15 27001 = 145982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27001 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27001) = 3 ^ 11 * m + 145982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27001.1, data_15_27001.2]

/-- Complete interval computation for depth 15, residue 27002. -/
theorem bounds_15_27002 : exactInterval 15 27002 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27002 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27002) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27002 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27002 : oddCount 27002 15 = 9 ∧ acceleratedOrbit 15 27002 = 16226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27002 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27002) = 3 ^ 9 * m + 16226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27002.1, data_15_27002.2]

/-- Complete interval computation for depth 15, residue 27003. -/
theorem bounds_15_27003 : exactInterval 15 27003 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27003 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27003) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27003 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27003 : oddCount 27003 15 = 9 ∧ acceleratedOrbit 15 27003 = 16222 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27003 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27003) = 3 ^ 9 * m + 16222 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27003.1, data_15_27003.2]

/-- Complete interval computation for depth 15, residue 27004. -/
theorem bounds_15_27004 : exactInterval 15 27004 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27004 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27004) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27004 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27004 : oddCount 27004 15 = 9 ∧ acceleratedOrbit 15 27004 = 16226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27004 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27004) = 3 ^ 9 * m + 16226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27004.1, data_15_27004.2]

/-- Complete interval computation for depth 15, residue 27005. -/
theorem bounds_15_27005 : exactInterval 15 27005 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27005 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27005) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27005 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27005 : oddCount 27005 15 = 9 ∧ acceleratedOrbit 15 27005 = 16226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27005 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27005) = 3 ^ 9 * m + 16226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27005.1, data_15_27005.2]

/-- Complete interval computation for depth 15, residue 27006. -/
theorem bounds_15_27006 : exactInterval 15 27006 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27006 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27006) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27006 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27006 : oddCount 27006 15 = 10 ∧ acceleratedOrbit 15 27006 = 48671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27006 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27006) = 3 ^ 10 * m + 48671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27006.1, data_15_27006.2]

/-- Complete interval computation for depth 15, residue 27007. -/
theorem bounds_15_27007 : exactInterval 15 27007 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27007 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27007) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27007 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27007 : oddCount 27007 15 = 10 ∧ acceleratedOrbit 15 27007 = 48671 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27007 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27007) = 3 ^ 10 * m + 48671 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27007.1, data_15_27007.2]

/-- Complete interval computation for depth 15, residue 27008. -/
theorem bounds_15_27008 : exactInterval 15 27008 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27008 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27008) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27008 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27008 : oddCount 27008 15 = 5 ∧ acceleratedOrbit 15 27008 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27008 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27008) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27008.1, data_15_27008.2]

/-- Complete interval computation for depth 15, residue 27009. -/
theorem bounds_15_27009 : exactInterval 15 27009 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27009 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27009) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27009 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27009 : oddCount 27009 15 = 6 ∧ acceleratedOrbit 15 27009 = 601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27009 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27009) = 3 ^ 6 * m + 601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27009.1, data_15_27009.2]

/-- Complete interval computation for depth 15, residue 27010. -/
theorem bounds_15_27010 : exactInterval 15 27010 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27010 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27010) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27010 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27010 : oddCount 27010 15 = 7 ∧ acceleratedOrbit 15 27010 = 1804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27010 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27010) = 3 ^ 7 * m + 1804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27010.1, data_15_27010.2]

/-- Complete interval computation for depth 15, residue 27011. -/
theorem bounds_15_27011 : exactInterval 15 27011 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27011 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27011) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27011 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27011 : oddCount 27011 15 = 7 ∧ acceleratedOrbit 15 27011 = 1804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27011 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27011) = 3 ^ 7 * m + 1804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27011.1, data_15_27011.2]

/-- Complete interval computation for depth 15, residue 27012. -/
theorem bounds_15_27012 : exactInterval 15 27012 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27012 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27012) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27012 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27012 : oddCount 27012 15 = 7 ∧ acceleratedOrbit 15 27012 = 1804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27012 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27012) = 3 ^ 7 * m + 1804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27012.1, data_15_27012.2]

/-- Complete interval computation for depth 15, residue 27013. -/
theorem bounds_15_27013 : exactInterval 15 27013 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27013 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27013) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27013 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27013 : oddCount 27013 15 = 7 ∧ acceleratedOrbit 15 27013 = 1804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27013 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27013) = 3 ^ 7 * m + 1804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27013.1, data_15_27013.2]

/-- Complete interval computation for depth 15, residue 27014. -/
theorem bounds_15_27014 : exactInterval 15 27014 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27014 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27014) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27014 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27014 : oddCount 27014 15 = 7 ∧ acceleratedOrbit 15 27014 = 1804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27014 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27014) = 3 ^ 7 * m + 1804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27014.1, data_15_27014.2]

/-- Complete interval computation for depth 15, residue 27015. -/
theorem bounds_15_27015 : exactInterval 15 27015 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27015 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27015) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27015 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27015 : oddCount 27015 15 = 7 ∧ acceleratedOrbit 15 27015 = 1804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27015 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27015) = 3 ^ 7 * m + 1804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27015.1, data_15_27015.2]

/-- Complete interval computation for depth 15, residue 27016. -/
theorem bounds_15_27016 : exactInterval 15 27016 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27016 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27016) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27016 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27016 : oddCount 27016 15 = 7 ∧ acceleratedOrbit 15 27016 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27016 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27016) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27016.1, data_15_27016.2]

/-- Complete interval computation for depth 15, residue 27017. -/
theorem bounds_15_27017 : exactInterval 15 27017 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27017 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27017) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27017 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27017 : oddCount 27017 15 = 8 ∧ acceleratedOrbit 15 27017 = 5410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27017 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27017) = 3 ^ 8 * m + 5410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27017.1, data_15_27017.2]

/-- Complete interval computation for depth 15, residue 27018. -/
theorem bounds_15_27018 : exactInterval 15 27018 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27018 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27018) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27018 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27018 : oddCount 27018 15 = 7 ∧ acceleratedOrbit 15 27018 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27018 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27018) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27018.1, data_15_27018.2]

/-- Complete interval computation for depth 15, residue 27019. -/
theorem bounds_15_27019 : exactInterval 15 27019 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27019 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27019) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27019 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27019 : oddCount 27019 15 = 8 ∧ acceleratedOrbit 15 27019 = 5411 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27019 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27019) = 3 ^ 8 * m + 5411 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27019.1, data_15_27019.2]

/-- Complete interval computation for depth 15, residue 27020. -/
theorem bounds_15_27020 : exactInterval 15 27020 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27020 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27020) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27020 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27020 : oddCount 27020 15 = 7 ∧ acceleratedOrbit 15 27020 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27020 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27020) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27020.1, data_15_27020.2]

/-- Complete interval computation for depth 15, residue 27021. -/
theorem bounds_15_27021 : exactInterval 15 27021 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27021 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27021) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27021 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27021 : oddCount 27021 15 = 7 ∧ acceleratedOrbit 15 27021 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27021 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27021) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27021.1, data_15_27021.2]

/-- Complete interval computation for depth 15, residue 27022. -/
theorem bounds_15_27022 : exactInterval 15 27022 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27022 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27022) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27022 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27022 : oddCount 27022 15 = 7 ∧ acceleratedOrbit 15 27022 = 1804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27022 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27022) = 3 ^ 7 * m + 1804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27022.1, data_15_27022.2]

/-- Complete interval computation for depth 15, residue 27023. -/
theorem bounds_15_27023 : exactInterval 15 27023 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27023 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27023) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27023 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27023 : oddCount 27023 15 = 7 ∧ acceleratedOrbit 15 27023 = 1804 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27023 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27023) = 3 ^ 7 * m + 1804 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27023.1, data_15_27023.2]

/-- Complete interval computation for depth 15, residue 27024. -/
theorem bounds_15_27024 : exactInterval 15 27024 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27024 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27024) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27024 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27024 : oddCount 27024 15 = 7 ∧ acceleratedOrbit 15 27024 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27024 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27024) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27024.1, data_15_27024.2]

/-- Complete interval computation for depth 15, residue 27025. -/
theorem bounds_15_27025 : exactInterval 15 27025 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27025 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27025) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27025 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27025 : oddCount 27025 15 = 6 ∧ acceleratedOrbit 15 27025 = 602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27025 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27025) = 3 ^ 6 * m + 602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27025.1, data_15_27025.2]

/-- Complete interval computation for depth 15, residue 27026. -/
theorem bounds_15_27026 : exactInterval 15 27026 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27026 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27026) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27026 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27026 : oddCount 27026 15 = 6 ∧ acceleratedOrbit 15 27026 = 602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27026 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27026) = 3 ^ 6 * m + 602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27026.1, data_15_27026.2]

/-- Complete interval computation for depth 15, residue 27027. -/
theorem bounds_15_27027 : exactInterval 15 27027 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27027 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27027) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27027 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27027 : oddCount 27027 15 = 6 ∧ acceleratedOrbit 15 27027 = 602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27027 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27027) = 3 ^ 6 * m + 602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27027.1, data_15_27027.2]

/-- Complete interval computation for depth 15, residue 27028. -/
theorem bounds_15_27028 : exactInterval 15 27028 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27028 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27028) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27028 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27028 : oddCount 27028 15 = 7 ∧ acceleratedOrbit 15 27028 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27028 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27028) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27028.1, data_15_27028.2]

/-- Complete interval computation for depth 15, residue 27029. -/
theorem bounds_15_27029 : exactInterval 15 27029 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27029 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27029) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27029 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27029 : oddCount 27029 15 = 7 ∧ acceleratedOrbit 15 27029 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27029 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27029) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27029.1, data_15_27029.2]

/-- Complete interval computation for depth 15, residue 27030. -/
theorem bounds_15_27030 : exactInterval 15 27030 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27030 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27030) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27030 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27030 : oddCount 27030 15 = 6 ∧ acceleratedOrbit 15 27030 = 602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27030 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27030) = 3 ^ 6 * m + 602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27030.1, data_15_27030.2]

/-- Complete interval computation for depth 15, residue 27031. -/
theorem bounds_15_27031 : exactInterval 15 27031 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27031 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27031) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27031 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27031 : oddCount 27031 15 = 6 ∧ acceleratedOrbit 15 27031 = 602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27031 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27031) = 3 ^ 6 * m + 602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27031.1, data_15_27031.2]

/-- Complete interval computation for depth 15, residue 27032. -/
theorem bounds_15_27032 : exactInterval 15 27032 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27032 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27032) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27032 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27032 : oddCount 27032 15 = 7 ∧ acceleratedOrbit 15 27032 = 1808 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27032 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27032) = 3 ^ 7 * m + 1808 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27032.1, data_15_27032.2]

end Collatz.Research.PassageAtlas.Batch0825
