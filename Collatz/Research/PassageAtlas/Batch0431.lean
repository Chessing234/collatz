import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0431

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14090. -/
theorem bounds_15_14090 : exactInterval 15 14090 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14090 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14090) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14090 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14090 : oddCount 14090 15 = 8 ∧ acceleratedOrbit 15 14090 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14090 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14090) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14090.1, data_15_14090.2]

/-- Complete interval computation for depth 15, residue 14091. -/
theorem bounds_15_14091 : exactInterval 15 14091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14091 : oddCount 14091 15 = 9 ∧ acceleratedOrbit 15 14091 = 8468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14091) = 3 ^ 9 * m + 8468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14091.1, data_15_14091.2]

/-- Complete interval computation for depth 15, residue 14092. -/
theorem bounds_15_14092 : exactInterval 15 14092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14092 : oddCount 14092 15 = 8 ∧ acceleratedOrbit 15 14092 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14092) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14092.1, data_15_14092.2]

/-- Complete interval computation for depth 15, residue 14093. -/
theorem bounds_15_14093 : exactInterval 15 14093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14093 : oddCount 14093 15 = 8 ∧ acceleratedOrbit 15 14093 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14093) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14093.1, data_15_14093.2]

/-- Complete interval computation for depth 15, residue 14094. -/
theorem bounds_15_14094 : exactInterval 15 14094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14094 : oddCount 14094 15 = 8 ∧ acceleratedOrbit 15 14094 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14094) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14094.1, data_15_14094.2]

/-- Complete interval computation for depth 15, residue 14095. -/
theorem bounds_15_14095 : exactInterval 15 14095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14095 : oddCount 14095 15 = 8 ∧ acceleratedOrbit 15 14095 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14095) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14095.1, data_15_14095.2]

/-- Complete interval computation for depth 15, residue 14096. -/
theorem bounds_15_14096 : exactInterval 15 14096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14096 : oddCount 14096 15 = 5 ∧ acceleratedOrbit 15 14096 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14096) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14096.1, data_15_14096.2]

/-- Complete interval computation for depth 15, residue 14097. -/
theorem bounds_15_14097 : exactInterval 15 14097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14097 : oddCount 14097 15 = 8 ∧ acceleratedOrbit 15 14097 = 2825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14097) = 3 ^ 8 * m + 2825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14097.1, data_15_14097.2]

/-- Complete interval computation for depth 15, residue 14098. -/
theorem bounds_15_14098 : exactInterval 15 14098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14098 : oddCount 14098 15 = 9 ∧ acceleratedOrbit 15 14098 = 8471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14098) = 3 ^ 9 * m + 8471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14098.1, data_15_14098.2]

/-- Complete interval computation for depth 15, residue 14099. -/
theorem bounds_15_14099 : exactInterval 15 14099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14099 : oddCount 14099 15 = 9 ∧ acceleratedOrbit 15 14099 = 8471 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14099) = 3 ^ 9 * m + 8471 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14099.1, data_15_14099.2]

/-- Complete interval computation for depth 15, residue 14100. -/
theorem bounds_15_14100 : exactInterval 15 14100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14100 : oddCount 14100 15 = 5 ∧ acceleratedOrbit 15 14100 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14100) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14100.1, data_15_14100.2]

/-- Complete interval computation for depth 15, residue 14101. -/
theorem bounds_15_14101 : exactInterval 15 14101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14101 : oddCount 14101 15 = 5 ∧ acceleratedOrbit 15 14101 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14101) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14101.1, data_15_14101.2]

/-- Complete interval computation for depth 15, residue 14102. -/
theorem bounds_15_14102 : exactInterval 15 14102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14102 : oddCount 14102 15 = 10 ∧ acceleratedOrbit 15 14102 = 25424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14102) = 3 ^ 10 * m + 25424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14102.1, data_15_14102.2]

/-- Complete interval computation for depth 15, residue 14103. -/
theorem bounds_15_14103 : exactInterval 15 14103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14103 : oddCount 14103 15 = 10 ∧ acceleratedOrbit 15 14103 = 25424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14103) = 3 ^ 10 * m + 25424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14103.1, data_15_14103.2]

/-- Complete interval computation for depth 15, residue 14104. -/
theorem bounds_15_14104 : exactInterval 15 14104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14104 : oddCount 14104 15 = 5 ∧ acceleratedOrbit 15 14104 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14104) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14104.1, data_15_14104.2]

/-- Complete interval computation for depth 15, residue 14105. -/
theorem bounds_15_14105 : exactInterval 15 14105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14105 : oddCount 14105 15 = 10 ∧ acceleratedOrbit 15 14105 = 25424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14105) = 3 ^ 10 * m + 25424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14105.1, data_15_14105.2]

/-- Complete interval computation for depth 15, residue 14106. -/
theorem bounds_15_14106 : exactInterval 15 14106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14106 : oddCount 14106 15 = 5 ∧ acceleratedOrbit 15 14106 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14106) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14106.1, data_15_14106.2]

/-- Complete interval computation for depth 15, residue 14107. -/
theorem bounds_15_14107 : exactInterval 15 14107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14107 : oddCount 14107 15 = 12 ∧ acceleratedOrbit 15 14107 = 228815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14107) = 3 ^ 12 * m + 228815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14107.1, data_15_14107.2]

/-- Complete interval computation for depth 15, residue 14108. -/
theorem bounds_15_14108 : exactInterval 15 14108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14108 : oddCount 14108 15 = 6 ∧ acceleratedOrbit 15 14108 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14108) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14108.1, data_15_14108.2]

/-- Complete interval computation for depth 15, residue 14109. -/
theorem bounds_15_14109 : exactInterval 15 14109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14109 : oddCount 14109 15 = 6 ∧ acceleratedOrbit 15 14109 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14109) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14109.1, data_15_14109.2]

/-- Complete interval computation for depth 15, residue 14110. -/
theorem bounds_15_14110 : exactInterval 15 14110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14110 : oddCount 14110 15 = 6 ∧ acceleratedOrbit 15 14110 = 314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14110) = 3 ^ 6 * m + 314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14110.1, data_15_14110.2]

/-- Complete interval computation for depth 15, residue 14111. -/
theorem bounds_15_14111 : exactInterval 15 14111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14111 : oddCount 14111 15 = 10 ∧ acceleratedOrbit 15 14111 = 25433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14111) = 3 ^ 10 * m + 25433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14111.1, data_15_14111.2]

/-- Complete interval computation for depth 15, residue 14112. -/
theorem bounds_15_14112 : exactInterval 15 14112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14112 : oddCount 14112 15 = 4 ∧ acceleratedOrbit 15 14112 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14112) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14112.1, data_15_14112.2]

/-- Complete interval computation for depth 15, residue 14113. -/
theorem bounds_15_14113 : exactInterval 15 14113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14113 : oddCount 14113 15 = 8 ∧ acceleratedOrbit 15 14113 = 2828 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14113) = 3 ^ 8 * m + 2828 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14113.1, data_15_14113.2]

/-- Complete interval computation for depth 15, residue 14114. -/
theorem bounds_15_14114 : exactInterval 15 14114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14114 : oddCount 14114 15 = 7 ∧ acceleratedOrbit 15 14114 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14114) = 3 ^ 7 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14114.1, data_15_14114.2]

/-- Complete interval computation for depth 15, residue 14115. -/
theorem bounds_15_14115 : exactInterval 15 14115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14115 : oddCount 14115 15 = 7 ∧ acceleratedOrbit 15 14115 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14115) = 3 ^ 7 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14115.1, data_15_14115.2]

/-- Complete interval computation for depth 15, residue 14116. -/
theorem bounds_15_14116 : exactInterval 15 14116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14116 : oddCount 14116 15 = 7 ∧ acceleratedOrbit 15 14116 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14116) = 3 ^ 7 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14116.1, data_15_14116.2]

/-- Complete interval computation for depth 15, residue 14117. -/
theorem bounds_15_14117 : exactInterval 15 14117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14117 : oddCount 14117 15 = 7 ∧ acceleratedOrbit 15 14117 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14117) = 3 ^ 7 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14117.1, data_15_14117.2]

/-- Complete interval computation for depth 15, residue 14118. -/
theorem bounds_15_14118 : exactInterval 15 14118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14118 : oddCount 14118 15 = 7 ∧ acceleratedOrbit 15 14118 = 944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14118) = 3 ^ 7 * m + 944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14118.1, data_15_14118.2]

/-- Complete interval computation for depth 15, residue 14119. -/
theorem bounds_15_14119 : exactInterval 15 14119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14119 : oddCount 14119 15 = 10 ∧ acceleratedOrbit 15 14119 = 25447 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14119) = 3 ^ 10 * m + 25447 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14119.1, data_15_14119.2]

/-- Complete interval computation for depth 15, residue 14120. -/
theorem bounds_15_14120 : exactInterval 15 14120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14120 : oddCount 14120 15 = 4 ∧ acceleratedOrbit 15 14120 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14120) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14120.1, data_15_14120.2]

/-- Complete interval computation for depth 15, residue 14121. -/
theorem bounds_15_14121 : exactInterval 15 14121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14121 : oddCount 14121 15 = 8 ∧ acceleratedOrbit 15 14121 = 2828 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14121) = 3 ^ 8 * m + 2828 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14121.1, data_15_14121.2]

/-- Complete interval computation for depth 15, residue 14122. -/
theorem bounds_15_14122 : exactInterval 15 14122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14122 : oddCount 14122 15 = 4 ∧ acceleratedOrbit 15 14122 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14122) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14122.1, data_15_14122.2]

end Collatz.Research.PassageAtlas.Batch0431
