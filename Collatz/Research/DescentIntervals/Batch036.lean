import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.DescentIntervals.Batch036

/-- Complete interval computation for depth 8, residue 103. -/
theorem bounds_8_103 : exactInterval 8 103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_103 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 103) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_103 : oddCount 103 8 = 7 ∧ acceleratedOrbit 8 103 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_103 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 103) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_103.1, data_8_103.2]

/-- Complete interval computation for depth 8, residue 104. -/
theorem bounds_8_104 : exactInterval 8 104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_104 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 104) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_104 : oddCount 104 8 = 2 ∧ acceleratedOrbit 8 104 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_104 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 104) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_104.1, data_8_104.2]

/-- Complete interval computation for depth 8, residue 105. -/
theorem bounds_8_105 : exactInterval 8 105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_105 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 105) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_105 : oddCount 105 8 = 5 ∧ acceleratedOrbit 8 105 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_105 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 105) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_105.1, data_8_105.2]

/-- Complete interval computation for depth 8, residue 106. -/
theorem bounds_8_106 : exactInterval 8 106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_106 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 106) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_106 : oddCount 106 8 = 2 ∧ acceleratedOrbit 8 106 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_106 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 106) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_106.1, data_8_106.2]

/-- Complete interval computation for depth 8, residue 107. -/
theorem bounds_8_107 : exactInterval 8 107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_107 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 107) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_107 : oddCount 107 8 = 5 ∧ acceleratedOrbit 8 107 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_107 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 107) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_107.1, data_8_107.2]

/-- Complete interval computation for depth 8, residue 108. -/
theorem bounds_8_108 : exactInterval 8 108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_108 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 108) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_108 : oddCount 108 8 = 5 ∧ acceleratedOrbit 8 108 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_108 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 108) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_108.1, data_8_108.2]

/-- Complete interval computation for depth 8, residue 109. -/
theorem bounds_8_109 : exactInterval 8 109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_109 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 109) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_109 : oddCount 109 8 = 5 ∧ acceleratedOrbit 8 109 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_109 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 109) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_109.1, data_8_109.2]

/-- Complete interval computation for depth 8, residue 110. -/
theorem bounds_8_110 : exactInterval 8 110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_110 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 110) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_110 : oddCount 110 8 = 5 ∧ acceleratedOrbit 8 110 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_110 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 110) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_110.1, data_8_110.2]

/-- Complete interval computation for depth 8, residue 111. -/
theorem bounds_8_111 : exactInterval 8 111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_111 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 111) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_111 : oddCount 111 8 = 6 ∧ acceleratedOrbit 8 111 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_111 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 111) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_111.1, data_8_111.2]

/-- Complete interval computation for depth 8, residue 112. -/
theorem bounds_8_112 : exactInterval 8 112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_8_112 (m : Nat) :
    stoppingTime (2 ^ 8 * m + 112) 8 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_8_112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_8_112 : oddCount 112 8 = 3 ∧ acceleratedOrbit 8 112 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_8_112 (m : Nat) :
    acceleratedOrbit 8 (2 ^ 8 * m + 112) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_8_112.1, data_8_112.2]

end Collatz.Research.DescentIntervals.Batch036
