import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0157

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5111. -/
theorem bounds_15_5111 : exactInterval 15 5111 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5111 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5111) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5111 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5111 : oddCount 5111 15 = 8 ∧ acceleratedOrbit 15 5111 = 1025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5111 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5111) = 3 ^ 8 * m + 1025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5111.1, data_15_5111.2]

/-- Complete interval computation for depth 15, residue 5112. -/
theorem bounds_15_5112 : exactInterval 15 5112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5112 : oddCount 5112 15 = 10 ∧ acceleratedOrbit 15 5112 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5112) = 3 ^ 10 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5112.1, data_15_5112.2]

/-- Complete interval computation for depth 15, residue 5113. -/
theorem bounds_15_5113 : exactInterval 15 5113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5113 : oddCount 5113 15 = 9 ∧ acceleratedOrbit 15 5113 = 3073 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5113) = 3 ^ 9 * m + 3073 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5113.1, data_15_5113.2]

/-- Complete interval computation for depth 15, residue 5114. -/
theorem bounds_15_5114 : exactInterval 15 5114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5114 : oddCount 5114 15 = 10 ∧ acceleratedOrbit 15 5114 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5114) = 3 ^ 10 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5114.1, data_15_5114.2]

/-- Complete interval computation for depth 15, residue 5115. -/
theorem bounds_15_5115 : exactInterval 15 5115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5115 : oddCount 5115 15 = 8 ∧ acceleratedOrbit 15 5115 = 1025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5115) = 3 ^ 8 * m + 1025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5115.1, data_15_5115.2]

/-- Complete interval computation for depth 15, residue 5116. -/
theorem bounds_15_5116 : exactInterval 15 5116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5116 : oddCount 5116 15 = 10 ∧ acceleratedOrbit 15 5116 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5116) = 3 ^ 10 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5116.1, data_15_5116.2]

/-- Complete interval computation for depth 15, residue 5117. -/
theorem bounds_15_5117 : exactInterval 15 5117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5117 : oddCount 5117 15 = 10 ∧ acceleratedOrbit 15 5117 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5117) = 3 ^ 10 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5117.1, data_15_5117.2]

/-- Complete interval computation for depth 15, residue 5118. -/
theorem bounds_15_5118 : exactInterval 15 5118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5118 : oddCount 5118 15 = 12 ∧ acceleratedOrbit 15 5118 = 83038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5118) = 3 ^ 12 * m + 83038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5118.1, data_15_5118.2]

/-- Complete interval computation for depth 15, residue 5119. -/
theorem bounds_15_5119 : exactInterval 15 5119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5119 : oddCount 5119 15 = 12 ∧ acceleratedOrbit 15 5119 = 83038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5119) = 3 ^ 12 * m + 83038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5119.1, data_15_5119.2]

/-- Complete interval computation for depth 15, residue 5120. -/
theorem bounds_15_5120 : exactInterval 15 5120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5120 : oddCount 5120 15 = 2 ∧ acceleratedOrbit 15 5120 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5120) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5120.1, data_15_5120.2]

/-- Complete interval computation for depth 15, residue 5121. -/
theorem bounds_15_5121 : exactInterval 15 5121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5121 : oddCount 5121 15 = 5 ∧ acceleratedOrbit 15 5121 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5121) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5121.1, data_15_5121.2]

/-- Complete interval computation for depth 15, residue 5122. -/
theorem bounds_15_5122 : exactInterval 15 5122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5122 : oddCount 5122 15 = 8 ∧ acceleratedOrbit 15 5122 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5122) = 3 ^ 8 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5122.1, data_15_5122.2]

/-- Complete interval computation for depth 15, residue 5123. -/
theorem bounds_15_5123 : exactInterval 15 5123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5123 : oddCount 5123 15 = 8 ∧ acceleratedOrbit 15 5123 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5123) = 3 ^ 8 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5123.1, data_15_5123.2]

/-- Complete interval computation for depth 15, residue 5124. -/
theorem bounds_15_5124 : exactInterval 15 5124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5124 : oddCount 5124 15 = 7 ∧ acceleratedOrbit 15 5124 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5124) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5124.1, data_15_5124.2]

/-- Complete interval computation for depth 15, residue 5125. -/
theorem bounds_15_5125 : exactInterval 15 5125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5125 : oddCount 5125 15 = 7 ∧ acceleratedOrbit 15 5125 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5125) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5125.1, data_15_5125.2]

/-- Complete interval computation for depth 15, residue 5126. -/
theorem bounds_15_5126 : exactInterval 15 5126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5126 : oddCount 5126 15 = 7 ∧ acceleratedOrbit 15 5126 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5126) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5126.1, data_15_5126.2]

/-- Complete interval computation for depth 15, residue 5127. -/
theorem bounds_15_5127 : exactInterval 15 5127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5127 : oddCount 5127 15 = 8 ∧ acceleratedOrbit 15 5127 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5127) = 3 ^ 8 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5127.1, data_15_5127.2]

/-- Complete interval computation for depth 15, residue 5128. -/
theorem bounds_15_5128 : exactInterval 15 5128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5128 : oddCount 5128 15 = 7 ∧ acceleratedOrbit 15 5128 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5128) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5128.1, data_15_5128.2]

/-- Complete interval computation for depth 15, residue 5129. -/
theorem bounds_15_5129 : exactInterval 15 5129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5129 : oddCount 5129 15 = 8 ∧ acceleratedOrbit 15 5129 = 1028 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5129) = 3 ^ 8 * m + 1028 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5129.1, data_15_5129.2]

/-- Complete interval computation for depth 15, residue 5130. -/
theorem bounds_15_5130 : exactInterval 15 5130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5130 : oddCount 5130 15 = 7 ∧ acceleratedOrbit 15 5130 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5130) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5130.1, data_15_5130.2]

/-- Complete interval computation for depth 15, residue 5131. -/
theorem bounds_15_5131 : exactInterval 15 5131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5131 : oddCount 5131 15 = 7 ∧ acceleratedOrbit 15 5131 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5131) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5131.1, data_15_5131.2]

/-- Complete interval computation for depth 15, residue 5132. -/
theorem bounds_15_5132 : exactInterval 15 5132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5132 : oddCount 5132 15 = 7 ∧ acceleratedOrbit 15 5132 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5132) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5132.1, data_15_5132.2]

/-- Complete interval computation for depth 15, residue 5133. -/
theorem bounds_15_5133 : exactInterval 15 5133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5133 : oddCount 5133 15 = 7 ∧ acceleratedOrbit 15 5133 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5133) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5133.1, data_15_5133.2]

/-- Complete interval computation for depth 15, residue 5134. -/
theorem bounds_15_5134 : exactInterval 15 5134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5134 : oddCount 5134 15 = 7 ∧ acceleratedOrbit 15 5134 = 343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5134) = 3 ^ 7 * m + 343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5134.1, data_15_5134.2]

/-- Complete interval computation for depth 15, residue 5135. -/
theorem bounds_15_5135 : exactInterval 15 5135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5135 : oddCount 5135 15 = 7 ∧ acceleratedOrbit 15 5135 = 343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5135) = 3 ^ 7 * m + 343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5135.1, data_15_5135.2]

/-- Complete interval computation for depth 15, residue 5136. -/
theorem bounds_15_5136 : exactInterval 15 5136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5136 : oddCount 5136 15 = 4 ∧ acceleratedOrbit 15 5136 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5136) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5136.1, data_15_5136.2]

/-- Complete interval computation for depth 15, residue 5137. -/
theorem bounds_15_5137 : exactInterval 15 5137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5137 : oddCount 5137 15 = 7 ∧ acceleratedOrbit 15 5137 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5137) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5137.1, data_15_5137.2]

/-- Complete interval computation for depth 15, residue 5138. -/
theorem bounds_15_5138 : exactInterval 15 5138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5138 : oddCount 5138 15 = 7 ∧ acceleratedOrbit 15 5138 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5138) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5138.1, data_15_5138.2]

/-- Complete interval computation for depth 15, residue 5139. -/
theorem bounds_15_5139 : exactInterval 15 5139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5139 : oddCount 5139 15 = 7 ∧ acceleratedOrbit 15 5139 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5139) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5139.1, data_15_5139.2]

/-- Complete interval computation for depth 15, residue 5140. -/
theorem bounds_15_5140 : exactInterval 15 5140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5140 : oddCount 5140 15 = 4 ∧ acceleratedOrbit 15 5140 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5140) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5140.1, data_15_5140.2]

/-- Complete interval computation for depth 15, residue 5141. -/
theorem bounds_15_5141 : exactInterval 15 5141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5141 : oddCount 5141 15 = 4 ∧ acceleratedOrbit 15 5141 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5141) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5141.1, data_15_5141.2]

/-- Complete interval computation for depth 15, residue 5142. -/
theorem bounds_15_5142 : exactInterval 15 5142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5142 : oddCount 5142 15 = 7 ∧ acceleratedOrbit 15 5142 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5142) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5142.1, data_15_5142.2]

/-- Complete interval computation for depth 15, residue 5143. -/
theorem bounds_15_5143 : exactInterval 15 5143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5143 : oddCount 5143 15 = 7 ∧ acceleratedOrbit 15 5143 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5143) = 3 ^ 7 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5143.1, data_15_5143.2]

end Collatz.Research.PassageAtlas.Batch0157
