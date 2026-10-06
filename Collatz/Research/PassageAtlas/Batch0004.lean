import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0004

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 98. -/
theorem bounds_15_98 : exactInterval 15 98 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_98 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 98) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_98 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_98 : oddCount 98 15 = 7 ∧ acceleratedOrbit 15 98 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_98 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 98) = 3 ^ 7 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_98.1, data_15_98.2]

/-- Complete interval computation for depth 15, residue 99. -/
theorem bounds_15_99 : exactInterval 15 99 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_99 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 99) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_99 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_99 : oddCount 99 15 = 7 ∧ acceleratedOrbit 15 99 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_99 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 99) = 3 ^ 7 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_99.1, data_15_99.2]

/-- Complete interval computation for depth 15, residue 100. -/
theorem bounds_15_100 : exactInterval 15 100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_100 : oddCount 100 15 = 7 ∧ acceleratedOrbit 15 100 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 100) = 3 ^ 7 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_100.1, data_15_100.2]

/-- Complete interval computation for depth 15, residue 101. -/
theorem bounds_15_101 : exactInterval 15 101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_101 : oddCount 101 15 = 7 ∧ acceleratedOrbit 15 101 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 101) = 3 ^ 7 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_101.1, data_15_101.2]

/-- Complete interval computation for depth 15, residue 102. -/
theorem bounds_15_102 : exactInterval 15 102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_102 : oddCount 102 15 = 7 ∧ acceleratedOrbit 15 102 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 102) = 3 ^ 7 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_102.1, data_15_102.2]

/-- Complete interval computation for depth 15, residue 103. -/
theorem bounds_15_103 : exactInterval 15 103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_103 : oddCount 103 15 = 11 ∧ acceleratedOrbit 15 103 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 103) = 3 ^ 11 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_103.1, data_15_103.2]

/-- Complete interval computation for depth 15, residue 104. -/
theorem bounds_15_104 : exactInterval 15 104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_104 : oddCount 104 15 = 5 ∧ acceleratedOrbit 15 104 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 104) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_104.1, data_15_104.2]

/-- Complete interval computation for depth 15, residue 105. -/
theorem bounds_15_105 : exactInterval 15 105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_105 : oddCount 105 15 = 8 ∧ acceleratedOrbit 15 105 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 105) = 3 ^ 8 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_105.1, data_15_105.2]

/-- Complete interval computation for depth 15, residue 106. -/
theorem bounds_15_106 : exactInterval 15 106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_106 : oddCount 106 15 = 5 ∧ acceleratedOrbit 15 106 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 106) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_106.1, data_15_106.2]

/-- Complete interval computation for depth 15, residue 107. -/
theorem bounds_15_107 : exactInterval 15 107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_107 : oddCount 107 15 = 11 ∧ acceleratedOrbit 15 107 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 107) = 3 ^ 11 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_107.1, data_15_107.2]

/-- Complete interval computation for depth 15, residue 108. -/
theorem bounds_15_108 : exactInterval 15 108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_108 : oddCount 108 15 = 10 ∧ acceleratedOrbit 15 108 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 108) = 3 ^ 10 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_108.1, data_15_108.2]

/-- Complete interval computation for depth 15, residue 109. -/
theorem bounds_15_109 : exactInterval 15 109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_109 : oddCount 109 15 = 10 ∧ acceleratedOrbit 15 109 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 109) = 3 ^ 10 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_109.1, data_15_109.2]

/-- Complete interval computation for depth 15, residue 110. -/
theorem bounds_15_110 : exactInterval 15 110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_110 : oddCount 110 15 = 10 ∧ acceleratedOrbit 15 110 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 110) = 3 ^ 10 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_110.1, data_15_110.2]

/-- Complete interval computation for depth 15, residue 111. -/
theorem bounds_15_111 : exactInterval 15 111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_111 : oddCount 111 15 = 12 ∧ acceleratedOrbit 15 111 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 111) = 3 ^ 12 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_111.1, data_15_111.2]

/-- Complete interval computation for depth 15, residue 112. -/
theorem bounds_15_112 : exactInterval 15 112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_112 : oddCount 112 15 = 5 ∧ acceleratedOrbit 15 112 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 112) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_112.1, data_15_112.2]

/-- Complete interval computation for depth 15, residue 113. -/
theorem bounds_15_113 : exactInterval 15 113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_113 : oddCount 113 15 = 5 ∧ acceleratedOrbit 15 113 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 113) = 3 ^ 5 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_113.1, data_15_113.2]

/-- Complete interval computation for depth 15, residue 114. -/
theorem bounds_15_114 : exactInterval 15 114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_114 : oddCount 114 15 = 8 ∧ acceleratedOrbit 15 114 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 114) = 3 ^ 8 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_114.1, data_15_114.2]

/-- Complete interval computation for depth 15, residue 115. -/
theorem bounds_15_115 : exactInterval 15 115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_115 : oddCount 115 15 = 8 ∧ acceleratedOrbit 15 115 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 115) = 3 ^ 8 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_115.1, data_15_115.2]

/-- Complete interval computation for depth 15, residue 116. -/
theorem bounds_15_116 : exactInterval 15 116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_116 : oddCount 116 15 = 5 ∧ acceleratedOrbit 15 116 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 116) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_116.1, data_15_116.2]

/-- Complete interval computation for depth 15, residue 117. -/
theorem bounds_15_117 : exactInterval 15 117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_117 : oddCount 117 15 = 5 ∧ acceleratedOrbit 15 117 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 117) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_117.1, data_15_117.2]

/-- Complete interval computation for depth 15, residue 118. -/
theorem bounds_15_118 : exactInterval 15 118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_118 : oddCount 118 15 = 8 ∧ acceleratedOrbit 15 118 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 118) = 3 ^ 8 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_118.1, data_15_118.2]

/-- Complete interval computation for depth 15, residue 119. -/
theorem bounds_15_119 : exactInterval 15 119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_119 : oddCount 119 15 = 8 ∧ acceleratedOrbit 15 119 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 119) = 3 ^ 8 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_119.1, data_15_119.2]

/-- Complete interval computation for depth 15, residue 120. -/
theorem bounds_15_120 : exactInterval 15 120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_120 : oddCount 120 15 = 5 ∧ acceleratedOrbit 15 120 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 120) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_120.1, data_15_120.2]

/-- Complete interval computation for depth 15, residue 121. -/
theorem bounds_15_121 : exactInterval 15 121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_121 : oddCount 121 15 = 11 ∧ acceleratedOrbit 15 121 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 121) = 3 ^ 11 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_121.1, data_15_121.2]

/-- Complete interval computation for depth 15, residue 122. -/
theorem bounds_15_122 : exactInterval 15 122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_122 : oddCount 122 15 = 5 ∧ acceleratedOrbit 15 122 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 122) = 3 ^ 5 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_122.1, data_15_122.2]

/-- Complete interval computation for depth 15, residue 123. -/
theorem bounds_15_123 : exactInterval 15 123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_123 : oddCount 123 15 = 9 ∧ acceleratedOrbit 15 123 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 123) = 3 ^ 9 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_123.1, data_15_123.2]

/-- Complete interval computation for depth 15, residue 124. -/
theorem bounds_15_124 : exactInterval 15 124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_124 : oddCount 124 15 = 10 ∧ acceleratedOrbit 15 124 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 124) = 3 ^ 10 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_124.1, data_15_124.2]

/-- Complete interval computation for depth 15, residue 125. -/
theorem bounds_15_125 : exactInterval 15 125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_125 : oddCount 125 15 = 10 ∧ acceleratedOrbit 15 125 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 125) = 3 ^ 10 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_125.1, data_15_125.2]

/-- Complete interval computation for depth 15, residue 126. -/
theorem bounds_15_126 : exactInterval 15 126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_126 : oddCount 126 15 = 10 ∧ acceleratedOrbit 15 126 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 126) = 3 ^ 10 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_126.1, data_15_126.2]

/-- Complete interval computation for depth 15, residue 127. -/
theorem bounds_15_127 : exactInterval 15 127 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 127) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_127 : oddCount 127 15 = 9 ∧ acceleratedOrbit 15 127 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 127) = 3 ^ 9 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_127.1, data_15_127.2]

/-- Complete interval computation for depth 15, residue 128. -/
theorem bounds_15_128 : exactInterval 15 128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_128 : oddCount 128 15 = 4 ∧ acceleratedOrbit 15 128 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 128) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_128.1, data_15_128.2]

/-- Complete interval computation for depth 15, residue 129. -/
theorem bounds_15_129 : exactInterval 15 129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_129 : oddCount 129 15 = 10 ∧ acceleratedOrbit 15 129 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 129) = 3 ^ 10 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_129.1, data_15_129.2]

/-- Complete interval computation for depth 15, residue 130. -/
theorem bounds_15_130 : exactInterval 15 130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_130 : oddCount 130 15 = 7 ∧ acceleratedOrbit 15 130 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 130) = 3 ^ 7 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_130.1, data_15_130.2]

end Collatz.Research.PassageAtlas.Batch0004
