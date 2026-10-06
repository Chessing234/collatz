import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0309

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10092. -/
theorem bounds_15_10092 : exactInterval 15 10092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10092 : oddCount 10092 15 = 8 ∧ acceleratedOrbit 15 10092 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10092) = 3 ^ 8 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10092.1, data_15_10092.2]

/-- Complete interval computation for depth 15, residue 10093. -/
theorem bounds_15_10093 : exactInterval 15 10093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10093 : oddCount 10093 15 = 8 ∧ acceleratedOrbit 15 10093 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10093) = 3 ^ 8 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10093.1, data_15_10093.2]

/-- Complete interval computation for depth 15, residue 10094. -/
theorem bounds_15_10094 : exactInterval 15 10094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10094 : oddCount 10094 15 = 8 ∧ acceleratedOrbit 15 10094 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10094) = 3 ^ 8 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10094.1, data_15_10094.2]

/-- Complete interval computation for depth 15, residue 10095. -/
theorem bounds_15_10095 : exactInterval 15 10095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10095 : oddCount 10095 15 = 11 ∧ acceleratedOrbit 15 10095 = 54584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10095) = 3 ^ 11 * m + 54584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10095.1, data_15_10095.2]

/-- Complete interval computation for depth 15, residue 10096. -/
theorem bounds_15_10096 : exactInterval 15 10096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10096 : oddCount 10096 15 = 4 ∧ acceleratedOrbit 15 10096 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10096) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10096.1, data_15_10096.2]

/-- Complete interval computation for depth 15, residue 10097. -/
theorem bounds_15_10097 : exactInterval 15 10097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10097 : oddCount 10097 15 = 4 ∧ acceleratedOrbit 15 10097 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10097) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10097.1, data_15_10097.2]

/-- Complete interval computation for depth 15, residue 10098. -/
theorem bounds_15_10098 : exactInterval 15 10098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10098 : oddCount 10098 15 = 9 ∧ acceleratedOrbit 15 10098 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10098) = 3 ^ 9 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10098.1, data_15_10098.2]

/-- Complete interval computation for depth 15, residue 10099. -/
theorem bounds_15_10099 : exactInterval 15 10099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10099 : oddCount 10099 15 = 9 ∧ acceleratedOrbit 15 10099 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10099) = 3 ^ 9 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10099.1, data_15_10099.2]

/-- Complete interval computation for depth 15, residue 10100. -/
theorem bounds_15_10100 : exactInterval 15 10100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10100 : oddCount 10100 15 = 4 ∧ acceleratedOrbit 15 10100 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10100) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10100.1, data_15_10100.2]

/-- Complete interval computation for depth 15, residue 10101. -/
theorem bounds_15_10101 : exactInterval 15 10101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10101 : oddCount 10101 15 = 4 ∧ acceleratedOrbit 15 10101 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10101) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10101.1, data_15_10101.2]

/-- Complete interval computation for depth 15, residue 10102. -/
theorem bounds_15_10102 : exactInterval 15 10102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10102 : oddCount 10102 15 = 9 ∧ acceleratedOrbit 15 10102 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10102) = 3 ^ 9 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10102.1, data_15_10102.2]

/-- Complete interval computation for depth 15, residue 10103. -/
theorem bounds_15_10103 : exactInterval 15 10103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10103 : oddCount 10103 15 = 9 ∧ acceleratedOrbit 15 10103 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10103) = 3 ^ 9 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10103.1, data_15_10103.2]

/-- Complete interval computation for depth 15, residue 10104. -/
theorem bounds_15_10104 : exactInterval 15 10104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10104 : oddCount 10104 15 = 11 ∧ acceleratedOrbit 15 10104 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10104) = 3 ^ 11 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10104.1, data_15_10104.2]

/-- Complete interval computation for depth 15, residue 10105. -/
theorem bounds_15_10105 : exactInterval 15 10105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10105 : oddCount 10105 15 = 10 ∧ acceleratedOrbit 15 10105 = 18215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10105) = 3 ^ 10 * m + 18215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10105.1, data_15_10105.2]

/-- Complete interval computation for depth 15, residue 10106. -/
theorem bounds_15_10106 : exactInterval 15 10106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10106 : oddCount 10106 15 = 11 ∧ acceleratedOrbit 15 10106 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10106) = 3 ^ 11 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10106.1, data_15_10106.2]

/-- Complete interval computation for depth 15, residue 10107. -/
theorem bounds_15_10107 : exactInterval 15 10107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10107 : oddCount 10107 15 = 10 ∧ acceleratedOrbit 15 10107 = 18218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10107) = 3 ^ 10 * m + 18218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10107.1, data_15_10107.2]

/-- Complete interval computation for depth 15, residue 10108. -/
theorem bounds_15_10108 : exactInterval 15 10108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10108 : oddCount 10108 15 = 11 ∧ acceleratedOrbit 15 10108 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10108) = 3 ^ 11 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10108.1, data_15_10108.2]

/-- Complete interval computation for depth 15, residue 10109. -/
theorem bounds_15_10109 : exactInterval 15 10109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10109 : oddCount 10109 15 = 11 ∧ acceleratedOrbit 15 10109 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10109) = 3 ^ 11 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10109.1, data_15_10109.2]

/-- Complete interval computation for depth 15, residue 10110. -/
theorem bounds_15_10110 : exactInterval 15 10110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10110 : oddCount 10110 15 = 11 ∧ acceleratedOrbit 15 10110 = 54668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10110) = 3 ^ 11 * m + 54668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10110.1, data_15_10110.2]

/-- Complete interval computation for depth 15, residue 10111. -/
theorem bounds_15_10111 : exactInterval 15 10111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10111 : oddCount 10111 15 = 11 ∧ acceleratedOrbit 15 10111 = 54668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10111) = 3 ^ 11 * m + 54668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10111.1, data_15_10111.2]

/-- Complete interval computation for depth 15, residue 10112. -/
theorem bounds_15_10112 : exactInterval 15 10112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10112 : oddCount 10112 15 = 5 ∧ acceleratedOrbit 15 10112 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10112) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10112.1, data_15_10112.2]

/-- Complete interval computation for depth 15, residue 10113. -/
theorem bounds_15_10113 : exactInterval 15 10113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10113 : oddCount 10113 15 = 8 ∧ acceleratedOrbit 15 10113 = 2026 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10113) = 3 ^ 8 * m + 2026 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10113.1, data_15_10113.2]

/-- Complete interval computation for depth 15, residue 10114. -/
theorem bounds_15_10114 : exactInterval 15 10114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10114 : oddCount 10114 15 = 7 ∧ acceleratedOrbit 15 10114 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10114) = 3 ^ 7 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10114.1, data_15_10114.2]

/-- Complete interval computation for depth 15, residue 10115. -/
theorem bounds_15_10115 : exactInterval 15 10115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10115 : oddCount 10115 15 = 7 ∧ acceleratedOrbit 15 10115 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10115) = 3 ^ 7 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10115.1, data_15_10115.2]

/-- Complete interval computation for depth 15, residue 10116. -/
theorem bounds_15_10116 : exactInterval 15 10116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10116 : oddCount 10116 15 = 7 ∧ acceleratedOrbit 15 10116 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10116) = 3 ^ 7 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10116.1, data_15_10116.2]

/-- Complete interval computation for depth 15, residue 10117. -/
theorem bounds_15_10117 : exactInterval 15 10117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10117 : oddCount 10117 15 = 7 ∧ acceleratedOrbit 15 10117 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10117) = 3 ^ 7 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10117.1, data_15_10117.2]

/-- Complete interval computation for depth 15, residue 10118. -/
theorem bounds_15_10118 : exactInterval 15 10118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10118 : oddCount 10118 15 = 7 ∧ acceleratedOrbit 15 10118 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10118) = 3 ^ 7 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10118.1, data_15_10118.2]

/-- Complete interval computation for depth 15, residue 10119. -/
theorem bounds_15_10119 : exactInterval 15 10119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10119 : oddCount 10119 15 = 7 ∧ acceleratedOrbit 15 10119 = 676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10119) = 3 ^ 7 * m + 676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10119.1, data_15_10119.2]

/-- Complete interval computation for depth 15, residue 10120. -/
theorem bounds_15_10120 : exactInterval 15 10120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10120 : oddCount 10120 15 = 5 ∧ acceleratedOrbit 15 10120 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10120) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10120.1, data_15_10120.2]

/-- Complete interval computation for depth 15, residue 10121. -/
theorem bounds_15_10121 : exactInterval 15 10121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10121 : oddCount 10121 15 = 8 ∧ acceleratedOrbit 15 10121 = 2027 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10121) = 3 ^ 8 * m + 2027 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10121.1, data_15_10121.2]

/-- Complete interval computation for depth 15, residue 10122. -/
theorem bounds_15_10122 : exactInterval 15 10122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10122 : oddCount 10122 15 = 5 ∧ acceleratedOrbit 15 10122 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10122) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10122.1, data_15_10122.2]

/-- Complete interval computation for depth 15, residue 10123. -/
theorem bounds_15_10123 : exactInterval 15 10123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10123 : oddCount 10123 15 = 9 ∧ acceleratedOrbit 15 10123 = 6083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10123) = 3 ^ 9 * m + 6083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10123.1, data_15_10123.2]

/-- Complete interval computation for depth 15, residue 10124. -/
theorem bounds_15_10124 : exactInterval 15 10124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10124 : oddCount 10124 15 = 5 ∧ acceleratedOrbit 15 10124 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10124) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10124.1, data_15_10124.2]

end Collatz.Research.PassageAtlas.Batch0309
