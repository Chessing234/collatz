import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0008

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 107. -/
theorem bounds_10_107 : exactInterval 10 107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_107 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 107) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_107 : oddCount 107 10 = 7 ∧ acceleratedOrbit 10 107 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_107 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 107) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_107.1, data_10_107.2]

/-- Complete interval computation for depth 10, residue 108. -/
theorem bounds_10_108 : exactInterval 10 108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_108 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 108) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_108 : oddCount 108 10 = 7 ∧ acceleratedOrbit 10 108 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_108 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 108) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_108.1, data_10_108.2]

/-- Complete interval computation for depth 10, residue 109. -/
theorem bounds_10_109 : exactInterval 10 109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_109 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 109) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_109 : oddCount 109 10 = 7 ∧ acceleratedOrbit 10 109 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_109 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 109) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_109.1, data_10_109.2]

/-- Complete interval computation for depth 10, residue 110. -/
theorem bounds_10_110 : exactInterval 10 110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_110 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 110) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_110 : oddCount 110 10 = 7 ∧ acceleratedOrbit 10 110 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_110 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 110) = 3 ^ 7 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_110.1, data_10_110.2]

/-- Complete interval computation for depth 10, residue 111. -/
theorem bounds_10_111 : exactInterval 10 111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_111 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 111) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_111 : oddCount 111 10 = 8 ∧ acceleratedOrbit 10 111 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_111 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 111) = 3 ^ 8 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_111.1, data_10_111.2]

/-- Complete interval computation for depth 10, residue 112. -/
theorem bounds_10_112 : exactInterval 10 112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_112 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 112) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_112 : oddCount 112 10 = 4 ∧ acceleratedOrbit 10 112 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_112 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 112) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_112.1, data_10_112.2]

/-- Complete interval computation for depth 10, residue 113. -/
theorem bounds_10_113 : exactInterval 10 113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_113 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 113) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_113 : oddCount 113 10 = 2 ∧ acceleratedOrbit 10 113 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_113 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 113) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_113.1, data_10_113.2]

/-- Complete interval computation for depth 10, residue 114. -/
theorem bounds_10_114 : exactInterval 10 114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_114 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 114) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_114 : oddCount 114 10 = 5 ∧ acceleratedOrbit 10 114 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_114 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 114) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_114.1, data_10_114.2]

/-- Complete interval computation for depth 10, residue 115. -/
theorem bounds_10_115 : exactInterval 10 115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_115 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 115) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_115 : oddCount 115 10 = 5 ∧ acceleratedOrbit 10 115 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_115 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 115) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_115.1, data_10_115.2]

/-- Complete interval computation for depth 10, residue 116. -/
theorem bounds_10_116 : exactInterval 10 116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_116 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 116) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_116 : oddCount 116 10 = 4 ∧ acceleratedOrbit 10 116 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_116 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 116) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_116.1, data_10_116.2]

/-- Complete interval computation for depth 10, residue 117. -/
theorem bounds_10_117 : exactInterval 10 117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_117 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 117) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_117 : oddCount 117 10 = 4 ∧ acceleratedOrbit 10 117 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_117 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 117) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_117.1, data_10_117.2]

/-- Complete interval computation for depth 10, residue 118. -/
theorem bounds_10_118 : exactInterval 10 118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_118 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 118) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_118 : oddCount 118 10 = 5 ∧ acceleratedOrbit 10 118 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_118 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 118) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_118.1, data_10_118.2]

/-- Complete interval computation for depth 10, residue 119. -/
theorem bounds_10_119 : exactInterval 10 119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_119 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 119) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_119 : oddCount 119 10 = 5 ∧ acceleratedOrbit 10 119 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_119 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 119) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_119.1, data_10_119.2]

/-- Complete interval computation for depth 10, residue 120. -/
theorem bounds_10_120 : exactInterval 10 120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_120 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 120) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_120 : oddCount 120 10 = 4 ∧ acceleratedOrbit 10 120 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_120 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 120) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_120.1, data_10_120.2]

/-- Complete interval computation for depth 10, residue 121. -/
theorem bounds_10_121 : exactInterval 10 121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_121 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 121) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_121 : oddCount 121 10 = 7 ∧ acceleratedOrbit 10 121 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_121 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 121) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_121.1, data_10_121.2]

end Collatz.Research.StoppingAtlas.Batch0008
