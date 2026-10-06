import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0930

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7101. -/
theorem bounds_13_7101 : exactInterval 13 7101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7101 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7101) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7101 : oddCount 7101 13 = 8 ∧ acceleratedOrbit 13 7101 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7101 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7101) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7101.1, data_13_7101.2]

/-- Complete interval computation for depth 13, residue 7102. -/
theorem bounds_13_7102 : exactInterval 13 7102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7102 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7102) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7102 : oddCount 7102 13 = 8 ∧ acceleratedOrbit 13 7102 = 5690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7102 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7102) = 3 ^ 8 * m + 5690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7102.1, data_13_7102.2]

/-- Complete interval computation for depth 13, residue 7103. -/
theorem bounds_13_7103 : exactInterval 13 7103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7103 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7103) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7103 : oddCount 7103 13 = 9 ∧ acceleratedOrbit 13 7103 = 17069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7103 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7103) = 3 ^ 9 * m + 17069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7103.1, data_13_7103.2]

/-- Complete interval computation for depth 13, residue 7104. -/
theorem bounds_13_7104 : exactInterval 13 7104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7104 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7104) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7104 : oddCount 7104 13 = 6 ∧ acceleratedOrbit 13 7104 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7104 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7104) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7104.1, data_13_7104.2]

/-- Complete interval computation for depth 13, residue 7105. -/
theorem bounds_13_7105 : exactInterval 13 7105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7105 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7105) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7105 : oddCount 7105 13 = 8 ∧ acceleratedOrbit 13 7105 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7105 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7105) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7105.1, data_13_7105.2]

/-- Complete interval computation for depth 13, residue 7106. -/
theorem bounds_13_7106 : exactInterval 13 7106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7106 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7106) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7106 : oddCount 7106 13 = 8 ∧ acceleratedOrbit 13 7106 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7106 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7106) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7106.1, data_13_7106.2]

/-- Complete interval computation for depth 13, residue 7107. -/
theorem bounds_13_7107 : exactInterval 13 7107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7107 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7107) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7107 : oddCount 7107 13 = 8 ∧ acceleratedOrbit 13 7107 = 5696 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7107 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7107) = 3 ^ 8 * m + 5696 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7107.1, data_13_7107.2]

/-- Complete interval computation for depth 13, residue 7108. -/
theorem bounds_13_7108 : exactInterval 13 7108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7108 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7108) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7108 : oddCount 7108 13 = 4 ∧ acceleratedOrbit 13 7108 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7108 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7108) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7108.1, data_13_7108.2]

/-- Complete interval computation for depth 13, residue 7109. -/
theorem bounds_13_7109 : exactInterval 13 7109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7109 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7109) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7109 : oddCount 7109 13 = 4 ∧ acceleratedOrbit 13 7109 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7109 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7109) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7109.1, data_13_7109.2]

/-- Complete interval computation for depth 13, residue 7110. -/
theorem bounds_13_7110 : exactInterval 13 7110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7110 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7110) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7110 : oddCount 7110 13 = 4 ∧ acceleratedOrbit 13 7110 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7110 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7110) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7110.1, data_13_7110.2]

/-- Complete interval computation for depth 13, residue 7111. -/
theorem bounds_13_7111 : exactInterval 13 7111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7111 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7111) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7111 : oddCount 7111 13 = 10 ∧ acceleratedOrbit 13 7111 = 51272 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7111 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7111) = 3 ^ 10 * m + 51272 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7111.1, data_13_7111.2]

/-- Complete interval computation for depth 13, residue 7112. -/
theorem bounds_13_7112 : exactInterval 13 7112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7112 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7112) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7112 : oddCount 7112 13 = 7 ∧ acceleratedOrbit 13 7112 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7112 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7112) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7112.1, data_13_7112.2]

/-- Complete interval computation for depth 13, residue 7113. -/
theorem bounds_13_7113 : exactInterval 13 7113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7113 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7113) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7113 : oddCount 7113 13 = 7 ∧ acceleratedOrbit 13 7113 = 1900 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7113 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7113) = 3 ^ 7 * m + 1900 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7113.1, data_13_7113.2]

/-- Complete interval computation for depth 13, residue 7114. -/
theorem bounds_13_7114 : exactInterval 13 7114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7114 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7114) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7114 : oddCount 7114 13 = 7 ∧ acceleratedOrbit 13 7114 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7114 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7114) = 3 ^ 7 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7114.1, data_13_7114.2]

/-- Complete interval computation for depth 13, residue 7115. -/
theorem bounds_13_7115 : exactInterval 13 7115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7115 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7115) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7115 : oddCount 7115 13 = 6 ∧ acceleratedOrbit 13 7115 = 634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7115 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7115) = 3 ^ 6 * m + 634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7115.1, data_13_7115.2]

end Collatz.Research.StoppingAtlas.Batch0930
