import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0981

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 32112. -/
theorem bounds_15_32112 : exactInterval 15 32112 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32112 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32112) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32112 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32112 : oddCount 32112 15 = 7 ∧ acceleratedOrbit 15 32112 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32112 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32112) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32112.1, data_15_32112.2]

/-- Complete interval computation for depth 15, residue 32113. -/
theorem bounds_15_32113 : exactInterval 15 32113 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32113 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32113) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32113 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32113 : oddCount 32113 15 = 7 ∧ acceleratedOrbit 15 32113 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32113 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32113) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32113.1, data_15_32113.2]

/-- Complete interval computation for depth 15, residue 32114. -/
theorem bounds_15_32114 : exactInterval 15 32114 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32114 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32114) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32114 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32114 : oddCount 32114 15 = 7 ∧ acceleratedOrbit 15 32114 = 2144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32114 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32114) = 3 ^ 7 * m + 2144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32114.1, data_15_32114.2]

/-- Complete interval computation for depth 15, residue 32115. -/
theorem bounds_15_32115 : exactInterval 15 32115 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32115 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32115) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32115 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32115 : oddCount 32115 15 = 7 ∧ acceleratedOrbit 15 32115 = 2144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32115 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32115) = 3 ^ 7 * m + 2144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32115.1, data_15_32115.2]

/-- Complete interval computation for depth 15, residue 32116. -/
theorem bounds_15_32116 : exactInterval 15 32116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32116 : oddCount 32116 15 = 7 ∧ acceleratedOrbit 15 32116 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32116) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32116.1, data_15_32116.2]

/-- Complete interval computation for depth 15, residue 32117. -/
theorem bounds_15_32117 : exactInterval 15 32117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32117 : oddCount 32117 15 = 7 ∧ acceleratedOrbit 15 32117 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32117) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32117.1, data_15_32117.2]

/-- Complete interval computation for depth 15, residue 32118. -/
theorem bounds_15_32118 : exactInterval 15 32118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32118 : oddCount 32118 15 = 7 ∧ acceleratedOrbit 15 32118 = 2144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32118) = 3 ^ 7 * m + 2144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32118.1, data_15_32118.2]

/-- Complete interval computation for depth 15, residue 32119. -/
theorem bounds_15_32119 : exactInterval 15 32119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32119 : oddCount 32119 15 = 7 ∧ acceleratedOrbit 15 32119 = 2144 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32119) = 3 ^ 7 * m + 2144 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32119.1, data_15_32119.2]

/-- Complete interval computation for depth 15, residue 32120. -/
theorem bounds_15_32120 : exactInterval 15 32120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32120 : oddCount 32120 15 = 6 ∧ acceleratedOrbit 15 32120 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32120) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32120.1, data_15_32120.2]

/-- Complete interval computation for depth 15, residue 32121. -/
theorem bounds_15_32121 : exactInterval 15 32121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32121 : oddCount 32121 15 = 11 ∧ acceleratedOrbit 15 32121 = 173663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32121) = 3 ^ 11 * m + 173663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32121.1, data_15_32121.2]

/-- Complete interval computation for depth 15, residue 32122. -/
theorem bounds_15_32122 : exactInterval 15 32122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32122 : oddCount 32122 15 = 6 ∧ acceleratedOrbit 15 32122 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32122) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32122.1, data_15_32122.2]

/-- Complete interval computation for depth 15, residue 32123. -/
theorem bounds_15_32123 : exactInterval 15 32123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32123 : oddCount 32123 15 = 9 ∧ acceleratedOrbit 15 32123 = 19298 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32123) = 3 ^ 9 * m + 19298 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32123.1, data_15_32123.2]

/-- Complete interval computation for depth 15, residue 32124. -/
theorem bounds_15_32124 : exactInterval 15 32124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32124 : oddCount 32124 15 = 6 ∧ acceleratedOrbit 15 32124 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32124) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32124.1, data_15_32124.2]

/-- Complete interval computation for depth 15, residue 32125. -/
theorem bounds_15_32125 : exactInterval 15 32125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32125 : oddCount 32125 15 = 6 ∧ acceleratedOrbit 15 32125 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32125) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32125.1, data_15_32125.2]

/-- Complete interval computation for depth 15, residue 32126. -/
theorem bounds_15_32126 : exactInterval 15 32126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32126 : oddCount 32126 15 = 11 ∧ acceleratedOrbit 15 32126 = 173690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32126) = 3 ^ 11 * m + 173690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32126.1, data_15_32126.2]

/-- Complete interval computation for depth 15, residue 32127. -/
theorem bounds_15_32127 : exactInterval 15 32127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32127 : oddCount 32127 15 = 11 ∧ acceleratedOrbit 15 32127 = 173690 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32127) = 3 ^ 11 * m + 173690 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32127.1, data_15_32127.2]

/-- Complete interval computation for depth 15, residue 32128. -/
theorem bounds_15_32128 : exactInterval 15 32128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32128 : oddCount 32128 15 = 6 ∧ acceleratedOrbit 15 32128 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32128) = 3 ^ 6 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32128.1, data_15_32128.2]

/-- Complete interval computation for depth 15, residue 32129. -/
theorem bounds_15_32129 : exactInterval 15 32129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32129 : oddCount 32129 15 = 9 ∧ acceleratedOrbit 15 32129 = 19304 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32129) = 3 ^ 9 * m + 19304 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32129.1, data_15_32129.2]

/-- Complete interval computation for depth 15, residue 32130. -/
theorem bounds_15_32130 : exactInterval 15 32130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32130 : oddCount 32130 15 = 7 ∧ acceleratedOrbit 15 32130 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32130) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32130.1, data_15_32130.2]

/-- Complete interval computation for depth 15, residue 32131. -/
theorem bounds_15_32131 : exactInterval 15 32131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32131 : oddCount 32131 15 = 7 ∧ acceleratedOrbit 15 32131 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32131) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32131.1, data_15_32131.2]

/-- Complete interval computation for depth 15, residue 32132. -/
theorem bounds_15_32132 : exactInterval 15 32132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32132 : oddCount 32132 15 = 8 ∧ acceleratedOrbit 15 32132 = 6436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32132) = 3 ^ 8 * m + 6436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32132.1, data_15_32132.2]

/-- Complete interval computation for depth 15, residue 32133. -/
theorem bounds_15_32133 : exactInterval 15 32133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32133 : oddCount 32133 15 = 8 ∧ acceleratedOrbit 15 32133 = 6436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32133) = 3 ^ 8 * m + 6436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32133.1, data_15_32133.2]

/-- Complete interval computation for depth 15, residue 32134. -/
theorem bounds_15_32134 : exactInterval 15 32134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32134 : oddCount 32134 15 = 8 ∧ acceleratedOrbit 15 32134 = 6436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32134) = 3 ^ 8 * m + 6436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32134.1, data_15_32134.2]

/-- Complete interval computation for depth 15, residue 32135. -/
theorem bounds_15_32135 : exactInterval 15 32135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32135 : oddCount 32135 15 = 7 ∧ acceleratedOrbit 15 32135 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32135) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32135.1, data_15_32135.2]

/-- Complete interval computation for depth 15, residue 32136. -/
theorem bounds_15_32136 : exactInterval 15 32136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32136 : oddCount 32136 15 = 4 ∧ acceleratedOrbit 15 32136 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32136) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32136.1, data_15_32136.2]

/-- Complete interval computation for depth 15, residue 32137. -/
theorem bounds_15_32137 : exactInterval 15 32137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32137 : oddCount 32137 15 = 6 ∧ acceleratedOrbit 15 32137 = 715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32137) = 3 ^ 6 * m + 715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32137.1, data_15_32137.2]

/-- Complete interval computation for depth 15, residue 32138. -/
theorem bounds_15_32138 : exactInterval 15 32138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32138 : oddCount 32138 15 = 4 ∧ acceleratedOrbit 15 32138 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32138) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32138.1, data_15_32138.2]

/-- Complete interval computation for depth 15, residue 32139. -/
theorem bounds_15_32139 : exactInterval 15 32139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32139 : oddCount 32139 15 = 8 ∧ acceleratedOrbit 15 32139 = 6436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32139) = 3 ^ 8 * m + 6436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32139.1, data_15_32139.2]

/-- Complete interval computation for depth 15, residue 32140. -/
theorem bounds_15_32140 : exactInterval 15 32140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32140 : oddCount 32140 15 = 4 ∧ acceleratedOrbit 15 32140 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32140) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32140.1, data_15_32140.2]

/-- Complete interval computation for depth 15, residue 32141. -/
theorem bounds_15_32141 : exactInterval 15 32141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32141 : oddCount 32141 15 = 4 ∧ acceleratedOrbit 15 32141 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32141) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32141.1, data_15_32141.2]

/-- Complete interval computation for depth 15, residue 32142. -/
theorem bounds_15_32142 : exactInterval 15 32142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32142 : oddCount 32142 15 = 7 ∧ acceleratedOrbit 15 32142 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32142) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32142.1, data_15_32142.2]

/-- Complete interval computation for depth 15, residue 32143. -/
theorem bounds_15_32143 : exactInterval 15 32143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32143 : oddCount 32143 15 = 7 ∧ acceleratedOrbit 15 32143 = 2146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32143) = 3 ^ 7 * m + 2146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32143.1, data_15_32143.2]

/-- Complete interval computation for depth 15, residue 32144. -/
theorem bounds_15_32144 : exactInterval 15 32144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_32144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 32144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_32144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_32144 : oddCount 32144 15 = 4 ∧ acceleratedOrbit 15 32144 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_32144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 32144) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_32144.1, data_15_32144.2]

end Collatz.Research.PassageAtlas.Batch0981
