import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0800

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5104. -/
theorem bounds_13_5104 : exactInterval 13 5104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5104 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5104) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5104 : oddCount 5104 13 = 7 ∧ acceleratedOrbit 13 5104 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5104 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5104) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5104.1, data_13_5104.2]

/-- Complete interval computation for depth 13, residue 5105. -/
theorem bounds_13_5105 : exactInterval 13 5105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5105 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5105) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5105 : oddCount 5105 13 = 7 ∧ acceleratedOrbit 13 5105 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5105 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5105) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5105.1, data_13_5105.2]

/-- Complete interval computation for depth 13, residue 5106. -/
theorem bounds_13_5106 : exactInterval 13 5106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5106 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5106) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5106 : oddCount 5106 13 = 8 ∧ acceleratedOrbit 13 5106 = 4094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5106 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5106) = 3 ^ 8 * m + 4094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5106.1, data_13_5106.2]

/-- Complete interval computation for depth 13, residue 5107. -/
theorem bounds_13_5107 : exactInterval 13 5107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5107 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5107) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5107 : oddCount 5107 13 = 8 ∧ acceleratedOrbit 13 5107 = 4094 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5107 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5107) = 3 ^ 8 * m + 4094 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5107.1, data_13_5107.2]

/-- Complete interval computation for depth 13, residue 5108. -/
theorem bounds_13_5108 : exactInterval 13 5108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5108 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5108) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5108 : oddCount 5108 13 = 7 ∧ acceleratedOrbit 13 5108 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5108 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5108) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5108.1, data_13_5108.2]

/-- Complete interval computation for depth 13, residue 5109. -/
theorem bounds_13_5109 : exactInterval 13 5109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5109 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5109) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5109 : oddCount 5109 13 = 7 ∧ acceleratedOrbit 13 5109 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5109 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5109) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5109.1, data_13_5109.2]

/-- Complete interval computation for depth 13, residue 5110. -/
theorem bounds_13_5110 : exactInterval 13 5110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5110 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5110) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5110 : oddCount 5110 13 = 6 ∧ acceleratedOrbit 13 5110 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5110 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5110) = 3 ^ 6 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5110.1, data_13_5110.2]

/-- Complete interval computation for depth 13, residue 5111. -/
theorem bounds_13_5111 : exactInterval 13 5111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5111 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5111) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5111 : oddCount 5111 13 = 6 ∧ acceleratedOrbit 13 5111 = 455 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5111 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5111) = 3 ^ 6 * m + 455 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5111.1, data_13_5111.2]

/-- Complete interval computation for depth 13, residue 5112. -/
theorem bounds_13_5112 : exactInterval 13 5112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5112 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5112) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5112 : oddCount 5112 13 = 9 ∧ acceleratedOrbit 13 5112 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5112 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5112) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5112.1, data_13_5112.2]

/-- Complete interval computation for depth 13, residue 5113. -/
theorem bounds_13_5113 : exactInterval 13 5113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5113 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5113) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5113 : oddCount 5113 13 = 8 ∧ acceleratedOrbit 13 5113 = 4097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5113 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5113) = 3 ^ 8 * m + 4097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5113.1, data_13_5113.2]

/-- Complete interval computation for depth 13, residue 5114. -/
theorem bounds_13_5114 : exactInterval 13 5114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5114 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5114) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5114 : oddCount 5114 13 = 9 ∧ acceleratedOrbit 13 5114 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5114 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5114) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5114.1, data_13_5114.2]

/-- Complete interval computation for depth 13, residue 5115. -/
theorem bounds_13_5115 : exactInterval 13 5115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5115 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5115) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5115 : oddCount 5115 13 = 7 ∧ acceleratedOrbit 13 5115 = 1366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5115 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5115) = 3 ^ 7 * m + 1366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5115.1, data_13_5115.2]

/-- Complete interval computation for depth 13, residue 5116. -/
theorem bounds_13_5116 : exactInterval 13 5116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5116 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5116) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5116 : oddCount 5116 13 = 9 ∧ acceleratedOrbit 13 5116 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5116 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5116) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5116.1, data_13_5116.2]

/-- Complete interval computation for depth 13, residue 5117. -/
theorem bounds_13_5117 : exactInterval 13 5117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5117 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5117) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5117 : oddCount 5117 13 = 9 ∧ acceleratedOrbit 13 5117 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5117 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5117) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5117.1, data_13_5117.2]

/-- Complete interval computation for depth 13, residue 5118. -/
theorem bounds_13_5118 : exactInterval 13 5118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5118 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5118) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5118 : oddCount 5118 13 = 11 ∧ acceleratedOrbit 13 5118 = 110717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5118 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5118) = 3 ^ 11 * m + 110717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5118.1, data_13_5118.2]

/-- Complete interval computation for depth 13, residue 5119. -/
theorem bounds_13_5119 : exactInterval 13 5119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5119 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5119) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5119 : oddCount 5119 13 = 11 ∧ acceleratedOrbit 13 5119 = 110717 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5119 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5119) = 3 ^ 11 * m + 110717 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5119.1, data_13_5119.2]

end Collatz.Research.StoppingAtlas.Batch0800
