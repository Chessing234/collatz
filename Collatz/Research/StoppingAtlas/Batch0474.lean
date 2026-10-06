import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0474

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 97. -/
theorem bounds_13_97 : exactInterval 13 97 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_97 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 97) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_97 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_97 : oddCount 97 13 = 9 ∧ acceleratedOrbit 13 97 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_97 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 97) = 3 ^ 9 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_97.1, data_13_97.2]

/-- Complete interval computation for depth 13, residue 98. -/
theorem bounds_13_98 : exactInterval 13 98 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_98 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 98) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_98 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_98 : oddCount 98 13 = 6 ∧ acceleratedOrbit 13 98 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_98 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 98) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_98.1, data_13_98.2]

/-- Complete interval computation for depth 13, residue 99. -/
theorem bounds_13_99 : exactInterval 13 99 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_99 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 99) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_99 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_99 : oddCount 99 13 = 6 ∧ acceleratedOrbit 13 99 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_99 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 99) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_99.1, data_13_99.2]

/-- Complete interval computation for depth 13, residue 100. -/
theorem bounds_13_100 : exactInterval 13 100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_100 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 100) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_100 : oddCount 100 13 = 6 ∧ acceleratedOrbit 13 100 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_100 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 100) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_100.1, data_13_100.2]

/-- Complete interval computation for depth 13, residue 101. -/
theorem bounds_13_101 : exactInterval 13 101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_101 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 101) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_101 : oddCount 101 13 = 6 ∧ acceleratedOrbit 13 101 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_101 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 101) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_101.1, data_13_101.2]

/-- Complete interval computation for depth 13, residue 102. -/
theorem bounds_13_102 : exactInterval 13 102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_102 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 102) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_102 : oddCount 102 13 = 6 ∧ acceleratedOrbit 13 102 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_102 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 102) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_102.1, data_13_102.2]

/-- Complete interval computation for depth 13, residue 103. -/
theorem bounds_13_103 : exactInterval 13 103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_103 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 103) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_103 : oddCount 103 13 = 9 ∧ acceleratedOrbit 13 103 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_103 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 103) = 3 ^ 9 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_103.1, data_13_103.2]

/-- Complete interval computation for depth 13, residue 104. -/
theorem bounds_13_104 : exactInterval 13 104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_104 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 104) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_104 : oddCount 104 13 = 4 ∧ acceleratedOrbit 13 104 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_104 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 104) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_104.1, data_13_104.2]

/-- Complete interval computation for depth 13, residue 105. -/
theorem bounds_13_105 : exactInterval 13 105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_105 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 105) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_105 : oddCount 105 13 = 7 ∧ acceleratedOrbit 13 105 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_105 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 105) = 3 ^ 7 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_105.1, data_13_105.2]

/-- Complete interval computation for depth 13, residue 106. -/
theorem bounds_13_106 : exactInterval 13 106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_106 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 106) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_106 : oddCount 106 13 = 4 ∧ acceleratedOrbit 13 106 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_106 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 106) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_106.1, data_13_106.2]

/-- Complete interval computation for depth 13, residue 107. -/
theorem bounds_13_107 : exactInterval 13 107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_107 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 107) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_107 : oddCount 107 13 = 9 ∧ acceleratedOrbit 13 107 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_107 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 107) = 3 ^ 9 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_107.1, data_13_107.2]

/-- Complete interval computation for depth 13, residue 108. -/
theorem bounds_13_108 : exactInterval 13 108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_108 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 108) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_108 : oddCount 108 13 = 8 ∧ acceleratedOrbit 13 108 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_108 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 108) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_108.1, data_13_108.2]

/-- Complete interval computation for depth 13, residue 109. -/
theorem bounds_13_109 : exactInterval 13 109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_109 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 109) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_109 : oddCount 109 13 = 8 ∧ acceleratedOrbit 13 109 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_109 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 109) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_109.1, data_13_109.2]

/-- Complete interval computation for depth 13, residue 110. -/
theorem bounds_13_110 : exactInterval 13 110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_110 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 110) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_110 : oddCount 110 13 = 8 ∧ acceleratedOrbit 13 110 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_110 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 110) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_110.1, data_13_110.2]

/-- Complete interval computation for depth 13, residue 111. -/
theorem bounds_13_111 : exactInterval 13 111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_111 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 111) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_111 : oddCount 111 13 = 11 ∧ acceleratedOrbit 13 111 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_111 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 111) = 3 ^ 11 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_111.1, data_13_111.2]

end Collatz.Research.StoppingAtlas.Batch0474
