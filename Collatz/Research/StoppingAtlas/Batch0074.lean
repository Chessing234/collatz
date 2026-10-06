import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0074

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 97. -/
theorem bounds_11_97 : exactInterval 11 97 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_97 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 97) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_97 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_97 : oddCount 97 11 = 7 ∧ acceleratedOrbit 11 97 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_97 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 97) = 3 ^ 7 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_97.1, data_11_97.2]

/-- Complete interval computation for depth 11, residue 98. -/
theorem bounds_11_98 : exactInterval 11 98 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_98 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 98) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_98 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_98 : oddCount 98 11 = 5 ∧ acceleratedOrbit 11 98 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_98 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 98) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_98.1, data_11_98.2]

/-- Complete interval computation for depth 11, residue 99. -/
theorem bounds_11_99 : exactInterval 11 99 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_99 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 99) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_99 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_99 : oddCount 99 11 = 5 ∧ acceleratedOrbit 11 99 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_99 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 99) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_99.1, data_11_99.2]

/-- Complete interval computation for depth 11, residue 100. -/
theorem bounds_11_100 : exactInterval 11 100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_100 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 100) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_100 : oddCount 100 11 = 5 ∧ acceleratedOrbit 11 100 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_100 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 100) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_100.1, data_11_100.2]

/-- Complete interval computation for depth 11, residue 101. -/
theorem bounds_11_101 : exactInterval 11 101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_101 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 101) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_101 : oddCount 101 11 = 5 ∧ acceleratedOrbit 11 101 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_101 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 101) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_101.1, data_11_101.2]

/-- Complete interval computation for depth 11, residue 102. -/
theorem bounds_11_102 : exactInterval 11 102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_102 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 102) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_102 : oddCount 102 11 = 5 ∧ acceleratedOrbit 11 102 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_102 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 102) = 3 ^ 5 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_102.1, data_11_102.2]

/-- Complete interval computation for depth 11, residue 103. -/
theorem bounds_11_103 : exactInterval 11 103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_103 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 103) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_103 : oddCount 103 11 = 8 ∧ acceleratedOrbit 11 103 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_103 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 103) = 3 ^ 8 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_103.1, data_11_103.2]

/-- Complete interval computation for depth 11, residue 104. -/
theorem bounds_11_104 : exactInterval 11 104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_104 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 104) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_104 : oddCount 104 11 = 3 ∧ acceleratedOrbit 11 104 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_104 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 104) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_104.1, data_11_104.2]

/-- Complete interval computation for depth 11, residue 105. -/
theorem bounds_11_105 : exactInterval 11 105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_105 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 105) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_105 : oddCount 105 11 = 6 ∧ acceleratedOrbit 11 105 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_105 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 105) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_105.1, data_11_105.2]

/-- Complete interval computation for depth 11, residue 106. -/
theorem bounds_11_106 : exactInterval 11 106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_106 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 106) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_106 : oddCount 106 11 = 3 ∧ acceleratedOrbit 11 106 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_106 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 106) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_106.1, data_11_106.2]

/-- Complete interval computation for depth 11, residue 107. -/
theorem bounds_11_107 : exactInterval 11 107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_107 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 107) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_107 : oddCount 107 11 = 8 ∧ acceleratedOrbit 11 107 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_107 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 107) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_107.1, data_11_107.2]

/-- Complete interval computation for depth 11, residue 108. -/
theorem bounds_11_108 : exactInterval 11 108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_108 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 108) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_108 : oddCount 108 11 = 7 ∧ acceleratedOrbit 11 108 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_108 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 108) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_108.1, data_11_108.2]

/-- Complete interval computation for depth 11, residue 109. -/
theorem bounds_11_109 : exactInterval 11 109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_109 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 109) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_109 : oddCount 109 11 = 7 ∧ acceleratedOrbit 11 109 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_109 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 109) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_109.1, data_11_109.2]

/-- Complete interval computation for depth 11, residue 110. -/
theorem bounds_11_110 : exactInterval 11 110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_110 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 110) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_110 : oddCount 110 11 = 7 ∧ acceleratedOrbit 11 110 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_110 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 110) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_110.1, data_11_110.2]

/-- Complete interval computation for depth 11, residue 111. -/
theorem bounds_11_111 : exactInterval 11 111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_111 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 111) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_111 : oddCount 111 11 = 9 ∧ acceleratedOrbit 11 111 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_111 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 111) = 3 ^ 9 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_111.1, data_11_111.2]

end Collatz.Research.StoppingAtlas.Batch0074
