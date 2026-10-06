import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0208

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 107. -/
theorem bounds_12_107 : exactInterval 12 107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_107 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 107) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_107 : oddCount 107 12 = 8 ∧ acceleratedOrbit 12 107 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_107 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 107) = 3 ^ 8 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_107.1, data_12_107.2]

/-- Complete interval computation for depth 12, residue 108. -/
theorem bounds_12_108 : exactInterval 12 108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_108 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 108) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_108 : oddCount 108 12 = 8 ∧ acceleratedOrbit 12 108 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_108 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 108) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_108.1, data_12_108.2]

/-- Complete interval computation for depth 12, residue 109. -/
theorem bounds_12_109 : exactInterval 12 109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_109 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 109) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_109 : oddCount 109 12 = 8 ∧ acceleratedOrbit 12 109 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_109 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 109) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_109.1, data_12_109.2]

/-- Complete interval computation for depth 12, residue 110. -/
theorem bounds_12_110 : exactInterval 12 110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_110 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 110) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_110 : oddCount 110 12 = 8 ∧ acceleratedOrbit 12 110 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_110 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 110) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_110.1, data_12_110.2]

/-- Complete interval computation for depth 12, residue 111. -/
theorem bounds_12_111 : exactInterval 12 111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_111 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 111) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_111 : oddCount 111 12 = 10 ∧ acceleratedOrbit 12 111 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_111 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 111) = 3 ^ 10 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_111.1, data_12_111.2]

/-- Complete interval computation for depth 12, residue 112. -/
theorem bounds_12_112 : exactInterval 12 112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_112 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 112) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_112 : oddCount 112 12 = 5 ∧ acceleratedOrbit 12 112 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_112 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 112) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_112.1, data_12_112.2]

/-- Complete interval computation for depth 12, residue 113. -/
theorem bounds_12_113 : exactInterval 12 113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_113 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 113) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_113 : oddCount 113 12 = 3 ∧ acceleratedOrbit 12 113 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_113 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 113) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_113.1, data_12_113.2]

/-- Complete interval computation for depth 12, residue 114. -/
theorem bounds_12_114 : exactInterval 12 114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_114 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 114) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_114 : oddCount 114 12 = 5 ∧ acceleratedOrbit 12 114 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_114 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 114) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_114.1, data_12_114.2]

/-- Complete interval computation for depth 12, residue 115. -/
theorem bounds_12_115 : exactInterval 12 115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_115 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 115) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_115 : oddCount 115 12 = 5 ∧ acceleratedOrbit 12 115 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_115 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 115) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_115.1, data_12_115.2]

/-- Complete interval computation for depth 12, residue 116. -/
theorem bounds_12_116 : exactInterval 12 116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_116 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 116) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_116 : oddCount 116 12 = 5 ∧ acceleratedOrbit 12 116 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_116 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 116) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_116.1, data_12_116.2]

/-- Complete interval computation for depth 12, residue 117. -/
theorem bounds_12_117 : exactInterval 12 117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_117 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 117) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_117 : oddCount 117 12 = 5 ∧ acceleratedOrbit 12 117 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_117 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 117) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_117.1, data_12_117.2]

/-- Complete interval computation for depth 12, residue 118. -/
theorem bounds_12_118 : exactInterval 12 118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_118 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 118) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_118 : oddCount 118 12 = 6 ∧ acceleratedOrbit 12 118 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_118 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 118) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_118.1, data_12_118.2]

/-- Complete interval computation for depth 12, residue 119. -/
theorem bounds_12_119 : exactInterval 12 119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_119 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 119) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_119 : oddCount 119 12 = 6 ∧ acceleratedOrbit 12 119 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_119 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 119) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_119.1, data_12_119.2]

/-- Complete interval computation for depth 12, residue 120. -/
theorem bounds_12_120 : exactInterval 12 120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_120 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 120) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_120 : oddCount 120 12 = 5 ∧ acceleratedOrbit 12 120 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_120 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 120) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_120.1, data_12_120.2]

/-- Complete interval computation for depth 12, residue 121. -/
theorem bounds_12_121 : exactInterval 12 121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_121 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 121) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_121 : oddCount 121 12 = 9 ∧ acceleratedOrbit 12 121 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_121 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 121) = 3 ^ 9 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_121.1, data_12_121.2]

end Collatz.Research.StoppingAtlas.Batch0208
