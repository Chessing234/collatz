import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch024

/-- Complete interval computation for depth 7, residue 109. -/
theorem bounds_7_109 : exactInterval 7 109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_109 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 109) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_109 : oddCount 109 7 = 4 ∧ acceleratedOrbit 7 109 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_109 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 109) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_109.1, data_7_109.2]

/-- Complete interval computation for depth 7, residue 110. -/
theorem bounds_7_110 : exactInterval 7 110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_110 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 110) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_110 : oddCount 110 7 = 4 ∧ acceleratedOrbit 7 110 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_110 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 110) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_110.1, data_7_110.2]

/-- Complete interval computation for depth 7, residue 111. -/
theorem bounds_7_111 : exactInterval 7 111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_111 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 111) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_111 : oddCount 111 7 = 6 ∧ acceleratedOrbit 7 111 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_111 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 111) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_111.1, data_7_111.2]

/-- Complete interval computation for depth 7, residue 112. -/
theorem bounds_7_112 : exactInterval 7 112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_112 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 112) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_112 : oddCount 112 7 = 3 ∧ acceleratedOrbit 7 112 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_112 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 112) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_112.1, data_7_112.2]

/-- Complete interval computation for depth 7, residue 113. -/
theorem bounds_7_113 : exactInterval 7 113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_113 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 113) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_113 : oddCount 113 7 = 2 ∧ acceleratedOrbit 7 113 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_113 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 113) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_113.1, data_7_113.2]

/-- Complete interval computation for depth 7, residue 114. -/
theorem bounds_7_114 : exactInterval 7 114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_114 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 114) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_114 : oddCount 114 7 = 4 ∧ acceleratedOrbit 7 114 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_114 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 114) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_114.1, data_7_114.2]

/-- Complete interval computation for depth 7, residue 115. -/
theorem bounds_7_115 : exactInterval 7 115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_115 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 115) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_115 : oddCount 115 7 = 4 ∧ acceleratedOrbit 7 115 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_115 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 115) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_115.1, data_7_115.2]

/-- Complete interval computation for depth 7, residue 116. -/
theorem bounds_7_116 : exactInterval 7 116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_116 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 116) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_116 : oddCount 116 7 = 3 ∧ acceleratedOrbit 7 116 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_116 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 116) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_116.1, data_7_116.2]

/-- Complete interval computation for depth 7, residue 117. -/
theorem bounds_7_117 : exactInterval 7 117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_117 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 117) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_117 : oddCount 117 7 = 3 ∧ acceleratedOrbit 7 117 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_117 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 117) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_117.1, data_7_117.2]

/-- Complete interval computation for depth 7, residue 118. -/
theorem bounds_7_118 : exactInterval 7 118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_7_118 (m : Nat) :
    stoppingTime (2 ^ 7 * m + 118) 7 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_7_118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_7_118 : oddCount 118 7 = 4 ∧ acceleratedOrbit 7 118 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_7_118 (m : Nat) :
    acceleratedOrbit 7 (2 ^ 7 * m + 118) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_7_118.1, data_7_118.2]

end Collatz.Research.DescentIntervals.Batch024
