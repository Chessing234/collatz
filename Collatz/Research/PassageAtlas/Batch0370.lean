import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0370

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12091. -/
theorem bounds_15_12091 : exactInterval 15 12091 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12091 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12091) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12091 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12091 : oddCount 12091 15 = 8 ∧ acceleratedOrbit 15 12091 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12091 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12091) = 3 ^ 8 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12091.1, data_15_12091.2]

/-- Complete interval computation for depth 15, residue 12092. -/
theorem bounds_15_12092 : exactInterval 15 12092 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12092 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12092) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12092 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12092 : oddCount 12092 15 = 8 ∧ acceleratedOrbit 15 12092 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12092 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12092) = 3 ^ 8 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12092.1, data_15_12092.2]

/-- Complete interval computation for depth 15, residue 12093. -/
theorem bounds_15_12093 : exactInterval 15 12093 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12093 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12093) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12093 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12093 : oddCount 12093 15 = 8 ∧ acceleratedOrbit 15 12093 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12093 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12093) = 3 ^ 8 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12093.1, data_15_12093.2]

/-- Complete interval computation for depth 15, residue 12094. -/
theorem bounds_15_12094 : exactInterval 15 12094 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12094 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12094) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12094 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12094 : oddCount 12094 15 = 8 ∧ acceleratedOrbit 15 12094 = 2422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12094 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12094) = 3 ^ 8 * m + 2422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12094.1, data_15_12094.2]

/-- Complete interval computation for depth 15, residue 12095. -/
theorem bounds_15_12095 : exactInterval 15 12095 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12095 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12095) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12095 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12095 : oddCount 12095 15 = 8 ∧ acceleratedOrbit 15 12095 = 2422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12095 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12095) = 3 ^ 8 * m + 2422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12095.1, data_15_12095.2]

/-- Complete interval computation for depth 15, residue 12096. -/
theorem bounds_15_12096 : exactInterval 15 12096 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12096 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12096) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12096 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12096 : oddCount 12096 15 = 5 ∧ acceleratedOrbit 15 12096 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12096 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12096) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12096.1, data_15_12096.2]

/-- Complete interval computation for depth 15, residue 12097. -/
theorem bounds_15_12097 : exactInterval 15 12097 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12097 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12097) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12097 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12097 : oddCount 12097 15 = 8 ∧ acceleratedOrbit 15 12097 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12097 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12097) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12097.1, data_15_12097.2]

/-- Complete interval computation for depth 15, residue 12098. -/
theorem bounds_15_12098 : exactInterval 15 12098 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12098 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12098) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12098 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12098 : oddCount 12098 15 = 7 ∧ acceleratedOrbit 15 12098 = 809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12098 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12098) = 3 ^ 7 * m + 809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12098.1, data_15_12098.2]

/-- Complete interval computation for depth 15, residue 12099. -/
theorem bounds_15_12099 : exactInterval 15 12099 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12099 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12099) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12099 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12099 : oddCount 12099 15 = 7 ∧ acceleratedOrbit 15 12099 = 809 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12099 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12099) = 3 ^ 7 * m + 809 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12099.1, data_15_12099.2]

/-- Complete interval computation for depth 15, residue 12100. -/
theorem bounds_15_12100 : exactInterval 15 12100 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12100 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12100) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12100 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12100 : oddCount 12100 15 = 8 ∧ acceleratedOrbit 15 12100 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12100 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12100) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12100.1, data_15_12100.2]

/-- Complete interval computation for depth 15, residue 12101. -/
theorem bounds_15_12101 : exactInterval 15 12101 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12101 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12101) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12101 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12101 : oddCount 12101 15 = 8 ∧ acceleratedOrbit 15 12101 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12101 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12101) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12101.1, data_15_12101.2]

/-- Complete interval computation for depth 15, residue 12102. -/
theorem bounds_15_12102 : exactInterval 15 12102 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12102 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12102) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12102 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12102 : oddCount 12102 15 = 8 ∧ acceleratedOrbit 15 12102 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12102 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12102) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12102.1, data_15_12102.2]

/-- Complete interval computation for depth 15, residue 12103. -/
theorem bounds_15_12103 : exactInterval 15 12103 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12103 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12103) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12103 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12103 : oddCount 12103 15 = 10 ∧ acceleratedOrbit 15 12103 = 21815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12103 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12103) = 3 ^ 10 * m + 21815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12103.1, data_15_12103.2]

/-- Complete interval computation for depth 15, residue 12104. -/
theorem bounds_15_12104 : exactInterval 15 12104 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12104 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12104) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12104 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12104 : oddCount 12104 15 = 9 ∧ acceleratedOrbit 15 12104 = 7280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12104 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12104) = 3 ^ 9 * m + 7280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12104.1, data_15_12104.2]

/-- Complete interval computation for depth 15, residue 12105. -/
theorem bounds_15_12105 : exactInterval 15 12105 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12105 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12105) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12105 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12105 : oddCount 12105 15 = 8 ∧ acceleratedOrbit 15 12105 = 2425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12105 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12105) = 3 ^ 8 * m + 2425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12105.1, data_15_12105.2]

/-- Complete interval computation for depth 15, residue 12106. -/
theorem bounds_15_12106 : exactInterval 15 12106 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12106 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12106) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12106 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12106 : oddCount 12106 15 = 9 ∧ acceleratedOrbit 15 12106 = 7280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12106 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12106) = 3 ^ 9 * m + 7280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12106.1, data_15_12106.2]

/-- Complete interval computation for depth 15, residue 12107. -/
theorem bounds_15_12107 : exactInterval 15 12107 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12107 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12107) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12107 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12107 : oddCount 12107 15 = 8 ∧ acceleratedOrbit 15 12107 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12107 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12107) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12107.1, data_15_12107.2]

/-- Complete interval computation for depth 15, residue 12108. -/
theorem bounds_15_12108 : exactInterval 15 12108 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12108 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12108) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12108 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12108 : oddCount 12108 15 = 9 ∧ acceleratedOrbit 15 12108 = 7280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12108 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12108) = 3 ^ 9 * m + 7280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12108.1, data_15_12108.2]

/-- Complete interval computation for depth 15, residue 12109. -/
theorem bounds_15_12109 : exactInterval 15 12109 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12109 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12109) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12109 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12109 : oddCount 12109 15 = 9 ∧ acceleratedOrbit 15 12109 = 7280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12109 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12109) = 3 ^ 9 * m + 7280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12109.1, data_15_12109.2]

/-- Complete interval computation for depth 15, residue 12110. -/
theorem bounds_15_12110 : exactInterval 15 12110 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12110 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12110) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12110 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12110 : oddCount 12110 15 = 10 ∧ acceleratedOrbit 15 12110 = 21829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12110 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12110) = 3 ^ 10 * m + 21829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12110.1, data_15_12110.2]

/-- Complete interval computation for depth 15, residue 12111. -/
theorem bounds_15_12111 : exactInterval 15 12111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12111 : oddCount 12111 15 = 10 ∧ acceleratedOrbit 15 12111 = 21829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12111) = 3 ^ 10 * m + 21829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12111.1, data_15_12111.2]

/-- Complete interval computation for depth 15, residue 12112. -/
theorem bounds_15_12112 : exactInterval 15 12112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12112 : oddCount 12112 15 = 5 ∧ acceleratedOrbit 15 12112 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12112) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12112.1, data_15_12112.2]

/-- Complete interval computation for depth 15, residue 12113. -/
theorem bounds_15_12113 : exactInterval 15 12113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12113 : oddCount 12113 15 = 9 ∧ acceleratedOrbit 15 12113 = 7280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12113) = 3 ^ 9 * m + 7280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12113.1, data_15_12113.2]

/-- Complete interval computation for depth 15, residue 12114. -/
theorem bounds_15_12114 : exactInterval 15 12114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12114 : oddCount 12114 15 = 10 ∧ acceleratedOrbit 15 12114 = 21836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12114) = 3 ^ 10 * m + 21836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12114.1, data_15_12114.2]

/-- Complete interval computation for depth 15, residue 12115. -/
theorem bounds_15_12115 : exactInterval 15 12115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12115 : oddCount 12115 15 = 10 ∧ acceleratedOrbit 15 12115 = 21836 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12115) = 3 ^ 10 * m + 21836 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12115.1, data_15_12115.2]

/-- Complete interval computation for depth 15, residue 12116. -/
theorem bounds_15_12116 : exactInterval 15 12116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12116 : oddCount 12116 15 = 5 ∧ acceleratedOrbit 15 12116 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12116) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12116.1, data_15_12116.2]

/-- Complete interval computation for depth 15, residue 12117. -/
theorem bounds_15_12117 : exactInterval 15 12117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12117 : oddCount 12117 15 = 5 ∧ acceleratedOrbit 15 12117 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12117) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12117.1, data_15_12117.2]

/-- Complete interval computation for depth 15, residue 12118. -/
theorem bounds_15_12118 : exactInterval 15 12118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12118 : oddCount 12118 15 = 9 ∧ acceleratedOrbit 15 12118 = 7283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12118) = 3 ^ 9 * m + 7283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12118.1, data_15_12118.2]

/-- Complete interval computation for depth 15, residue 12119. -/
theorem bounds_15_12119 : exactInterval 15 12119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12119 : oddCount 12119 15 = 9 ∧ acceleratedOrbit 15 12119 = 7283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12119) = 3 ^ 9 * m + 7283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12119.1, data_15_12119.2]

/-- Complete interval computation for depth 15, residue 12120. -/
theorem bounds_15_12120 : exactInterval 15 12120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12120 : oddCount 12120 15 = 10 ∧ acceleratedOrbit 15 12120 = 21869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12120) = 3 ^ 10 * m + 21869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12120.1, data_15_12120.2]

/-- Complete interval computation for depth 15, residue 12121. -/
theorem bounds_15_12121 : exactInterval 15 12121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12121 : oddCount 12121 15 = 9 ∧ acceleratedOrbit 15 12121 = 7289 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12121) = 3 ^ 9 * m + 7289 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12121.1, data_15_12121.2]

/-- Complete interval computation for depth 15, residue 12122. -/
theorem bounds_15_12122 : exactInterval 15 12122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12122 : oddCount 12122 15 = 10 ∧ acceleratedOrbit 15 12122 = 21869 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12122) = 3 ^ 10 * m + 21869 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12122.1, data_15_12122.2]

/-- Complete interval computation for depth 15, residue 12123. -/
theorem bounds_15_12123 : exactInterval 15 12123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12123 : oddCount 12123 15 = 11 ∧ acceleratedOrbit 15 12123 = 65549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12123) = 3 ^ 11 * m + 65549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12123.1, data_15_12123.2]

end Collatz.Research.PassageAtlas.Batch0370
