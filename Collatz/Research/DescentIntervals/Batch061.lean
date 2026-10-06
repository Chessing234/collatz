import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch061

/-- Complete interval computation for depth 9, residue 103. -/
theorem bounds_9_103 : exactInterval 9 103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_103 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 103) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_103 : oddCount 103 9 = 7 ∧ acceleratedOrbit 9 103 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_103 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 103) = 3 ^ 7 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_103.1, data_9_103.2]

/-- Complete interval computation for depth 9, residue 104. -/
theorem bounds_9_104 : exactInterval 9 104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_104 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 104) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_104 : oddCount 104 9 = 2 ∧ acceleratedOrbit 9 104 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_104 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 104) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_104.1, data_9_104.2]

/-- Complete interval computation for depth 9, residue 105. -/
theorem bounds_9_105 : exactInterval 9 105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_105 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 105) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_105 : oddCount 105 9 = 6 ∧ acceleratedOrbit 9 105 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_105 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 105) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_105.1, data_9_105.2]

/-- Complete interval computation for depth 9, residue 106. -/
theorem bounds_9_106 : exactInterval 9 106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_106 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 106) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_106 : oddCount 106 9 = 2 ∧ acceleratedOrbit 9 106 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_106 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 106) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_106.1, data_9_106.2]

/-- Complete interval computation for depth 9, residue 107. -/
theorem bounds_9_107 : exactInterval 9 107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_107 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 107) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_107 : oddCount 107 9 = 6 ∧ acceleratedOrbit 9 107 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_107 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 107) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_107.1, data_9_107.2]

/-- Complete interval computation for depth 9, residue 108. -/
theorem bounds_9_108 : exactInterval 9 108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_108 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 108) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_108 : oddCount 108 9 = 6 ∧ acceleratedOrbit 9 108 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_108 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 108) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_108.1, data_9_108.2]

/-- Complete interval computation for depth 9, residue 109. -/
theorem bounds_9_109 : exactInterval 9 109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_109 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 109) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_109 : oddCount 109 9 = 6 ∧ acceleratedOrbit 9 109 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_109 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 109) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_109.1, data_9_109.2]

/-- Complete interval computation for depth 9, residue 110. -/
theorem bounds_9_110 : exactInterval 9 110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_110 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 110) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_110 : oddCount 110 9 = 6 ∧ acceleratedOrbit 9 110 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_110 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 110) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_110.1, data_9_110.2]

/-- Complete interval computation for depth 9, residue 111. -/
theorem bounds_9_111 : exactInterval 9 111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_111 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 111) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_111 : oddCount 111 9 = 7 ∧ acceleratedOrbit 9 111 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_111 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 111) = 3 ^ 7 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_111.1, data_9_111.2]

/-- Complete interval computation for depth 9, residue 112. -/
theorem bounds_9_112 : exactInterval 9 112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_9_112 (m : Nat) :
    stoppingTime (2 ^ 9 * m + 112) 9 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_9_112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_9_112 : oddCount 112 9 = 4 ∧ acceleratedOrbit 9 112 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_9_112 (m : Nat) :
    acceleratedOrbit 9 (2 ^ 9 * m + 112) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_9_112.1, data_9_112.2]

end Collatz.Research.DescentIntervals.Batch061
