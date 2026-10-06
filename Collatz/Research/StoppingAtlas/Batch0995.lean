import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0995

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 8099. -/
theorem bounds_13_8099 : exactInterval 13 8099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8099 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8099) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8099 : oddCount 8099 13 = 6 ∧ acceleratedOrbit 13 8099 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8099 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8099) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8099.1, data_13_8099.2]

/-- Complete interval computation for depth 13, residue 8100. -/
theorem bounds_13_8100 : exactInterval 13 8100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8100 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8100) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8100 : oddCount 8100 13 = 8 ∧ acceleratedOrbit 13 8100 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8100 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8100) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8100.1, data_13_8100.2]

/-- Complete interval computation for depth 13, residue 8101. -/
theorem bounds_13_8101 : exactInterval 13 8101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8101 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8101) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8101 : oddCount 8101 13 = 8 ∧ acceleratedOrbit 13 8101 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8101 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8101) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8101.1, data_13_8101.2]

/-- Complete interval computation for depth 13, residue 8102. -/
theorem bounds_13_8102 : exactInterval 13 8102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8102 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8102) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8102 : oddCount 8102 13 = 8 ∧ acceleratedOrbit 13 8102 = 6493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8102 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8102) = 3 ^ 8 * m + 6493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8102.1, data_13_8102.2]

/-- Complete interval computation for depth 13, residue 8103. -/
theorem bounds_13_8103 : exactInterval 13 8103 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8103 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8103) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8103 : oddCount 8103 13 = 8 ∧ acceleratedOrbit 13 8103 = 6491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8103 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8103) = 3 ^ 8 * m + 6491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8103.1, data_13_8103.2]

/-- Complete interval computation for depth 13, residue 8104. -/
theorem bounds_13_8104 : exactInterval 13 8104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8104 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8104) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8104 : oddCount 8104 13 = 6 ∧ acceleratedOrbit 13 8104 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8104 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8104) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8104.1, data_13_8104.2]

/-- Complete interval computation for depth 13, residue 8105. -/
theorem bounds_13_8105 : exactInterval 13 8105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8105 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8105) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8105 : oddCount 8105 13 = 9 ∧ acceleratedOrbit 13 8105 = 19478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8105 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8105) = 3 ^ 9 * m + 19478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8105.1, data_13_8105.2]

/-- Complete interval computation for depth 13, residue 8106. -/
theorem bounds_13_8106 : exactInterval 13 8106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8106 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8106) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8106 : oddCount 8106 13 = 6 ∧ acceleratedOrbit 13 8106 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8106 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8106) = 3 ^ 6 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8106.1, data_13_8106.2]

/-- Complete interval computation for depth 13, residue 8107. -/
theorem bounds_13_8107 : exactInterval 13 8107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8107 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8107) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8107 : oddCount 8107 13 = 7 ∧ acceleratedOrbit 13 8107 = 2165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8107 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8107) = 3 ^ 7 * m + 2165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8107.1, data_13_8107.2]

/-- Complete interval computation for depth 13, residue 8108. -/
theorem bounds_13_8108 : exactInterval 13 8108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8108 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8108) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8108 : oddCount 8108 13 = 8 ∧ acceleratedOrbit 13 8108 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8108 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8108) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8108.1, data_13_8108.2]

/-- Complete interval computation for depth 13, residue 8109. -/
theorem bounds_13_8109 : exactInterval 13 8109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8109 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8109) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8109 : oddCount 8109 13 = 8 ∧ acceleratedOrbit 13 8109 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8109 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8109) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8109.1, data_13_8109.2]

/-- Complete interval computation for depth 13, residue 8110. -/
theorem bounds_13_8110 : exactInterval 13 8110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8110 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8110) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8110 : oddCount 8110 13 = 8 ∧ acceleratedOrbit 13 8110 = 6500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8110 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8110) = 3 ^ 8 * m + 6500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8110.1, data_13_8110.2]

/-- Complete interval computation for depth 13, residue 8111. -/
theorem bounds_13_8111 : exactInterval 13 8111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8111 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8111) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8111 : oddCount 8111 13 = 6 ∧ acceleratedOrbit 13 8111 = 722 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8111 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8111) = 3 ^ 6 * m + 722 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8111.1, data_13_8111.2]

/-- Complete interval computation for depth 13, residue 8112. -/
theorem bounds_13_8112 : exactInterval 13 8112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8112 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8112) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8112 : oddCount 8112 13 = 6 ∧ acceleratedOrbit 13 8112 = 724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8112 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8112) = 3 ^ 6 * m + 724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8112.1, data_13_8112.2]

/-- Complete interval computation for depth 13, residue 8113. -/
theorem bounds_13_8113 : exactInterval 13 8113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8113 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8113) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8113 : oddCount 8113 13 = 5 ∧ acceleratedOrbit 13 8113 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8113 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8113) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8113.1, data_13_8113.2]

/-- Complete interval computation for depth 13, residue 8114. -/
theorem bounds_13_8114 : exactInterval 13 8114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_8114 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 8114) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_8114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_8114 : oddCount 8114 13 = 5 ∧ acceleratedOrbit 13 8114 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_8114 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 8114) = 3 ^ 5 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_8114.1, data_13_8114.2]

end Collatz.Research.StoppingAtlas.Batch0995
