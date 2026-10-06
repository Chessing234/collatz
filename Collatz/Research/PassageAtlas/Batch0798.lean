import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0798

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26116. -/
theorem bounds_15_26116 : exactInterval 15 26116 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26116 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26116) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26116 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26116 : oddCount 26116 15 = 7 ∧ acceleratedOrbit 15 26116 = 1745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26116 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26116) = 3 ^ 7 * m + 1745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26116.1, data_15_26116.2]

/-- Complete interval computation for depth 15, residue 26117. -/
theorem bounds_15_26117 : exactInterval 15 26117 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26117 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26117) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26117 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26117 : oddCount 26117 15 = 7 ∧ acceleratedOrbit 15 26117 = 1745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26117 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26117) = 3 ^ 7 * m + 1745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26117.1, data_15_26117.2]

/-- Complete interval computation for depth 15, residue 26118. -/
theorem bounds_15_26118 : exactInterval 15 26118 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26118 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26118) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26118 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26118 : oddCount 26118 15 = 7 ∧ acceleratedOrbit 15 26118 = 1745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26118 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26118) = 3 ^ 7 * m + 1745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26118.1, data_15_26118.2]

/-- Complete interval computation for depth 15, residue 26119. -/
theorem bounds_15_26119 : exactInterval 15 26119 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26119 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26119) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26119 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26119 : oddCount 26119 15 = 8 ∧ acceleratedOrbit 15 26119 = 5231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26119 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26119) = 3 ^ 8 * m + 5231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26119.1, data_15_26119.2]

/-- Complete interval computation for depth 15, residue 26120. -/
theorem bounds_15_26120 : exactInterval 15 26120 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26120 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26120) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26120 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26120 : oddCount 26120 15 = 5 ∧ acceleratedOrbit 15 26120 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26120 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26120) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26120.1, data_15_26120.2]

/-- Complete interval computation for depth 15, residue 26121. -/
theorem bounds_15_26121 : exactInterval 15 26121 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26121 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26121) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26121 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26121 : oddCount 26121 15 = 8 ∧ acceleratedOrbit 15 26121 = 5231 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26121 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26121) = 3 ^ 8 * m + 5231 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26121.1, data_15_26121.2]

/-- Complete interval computation for depth 15, residue 26122. -/
theorem bounds_15_26122 : exactInterval 15 26122 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26122 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26122) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26122 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26122 : oddCount 26122 15 = 5 ∧ acceleratedOrbit 15 26122 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26122 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26122) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26122.1, data_15_26122.2]

/-- Complete interval computation for depth 15, residue 26123. -/
theorem bounds_15_26123 : exactInterval 15 26123 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26123 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26123) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26123 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26123 : oddCount 26123 15 = 7 ∧ acceleratedOrbit 15 26123 = 1745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26123 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26123) = 3 ^ 7 * m + 1745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26123.1, data_15_26123.2]

/-- Complete interval computation for depth 15, residue 26124. -/
theorem bounds_15_26124 : exactInterval 15 26124 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26124 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26124) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26124 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26124 : oddCount 26124 15 = 5 ∧ acceleratedOrbit 15 26124 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26124 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26124) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26124.1, data_15_26124.2]

/-- Complete interval computation for depth 15, residue 26125. -/
theorem bounds_15_26125 : exactInterval 15 26125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26125 : oddCount 26125 15 = 5 ∧ acceleratedOrbit 15 26125 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26125) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26125.1, data_15_26125.2]

/-- Complete interval computation for depth 15, residue 26126. -/
theorem bounds_15_26126 : exactInterval 15 26126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26126 : oddCount 26126 15 = 7 ∧ acceleratedOrbit 15 26126 = 1744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26126) = 3 ^ 7 * m + 1744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26126.1, data_15_26126.2]

/-- Complete interval computation for depth 15, residue 26127. -/
theorem bounds_15_26127 : exactInterval 15 26127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26127 : oddCount 26127 15 = 7 ∧ acceleratedOrbit 15 26127 = 1744 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26127) = 3 ^ 7 * m + 1744 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26127.1, data_15_26127.2]

/-- Complete interval computation for depth 15, residue 26128. -/
theorem bounds_15_26128 : exactInterval 15 26128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26128 : oddCount 26128 15 = 5 ∧ acceleratedOrbit 15 26128 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26128) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26128.1, data_15_26128.2]

/-- Complete interval computation for depth 15, residue 26129. -/
theorem bounds_15_26129 : exactInterval 15 26129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26129 : oddCount 26129 15 = 5 ∧ acceleratedOrbit 15 26129 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26129) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26129.1, data_15_26129.2]

/-- Complete interval computation for depth 15, residue 26130. -/
theorem bounds_15_26130 : exactInterval 15 26130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26130 : oddCount 26130 15 = 8 ∧ acceleratedOrbit 15 26130 = 5233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26130) = 3 ^ 8 * m + 5233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26130.1, data_15_26130.2]

/-- Complete interval computation for depth 15, residue 26131. -/
theorem bounds_15_26131 : exactInterval 15 26131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26131 : oddCount 26131 15 = 8 ∧ acceleratedOrbit 15 26131 = 5233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26131) = 3 ^ 8 * m + 5233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26131.1, data_15_26131.2]

/-- Complete interval computation for depth 15, residue 26132. -/
theorem bounds_15_26132 : exactInterval 15 26132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26132 : oddCount 26132 15 = 5 ∧ acceleratedOrbit 15 26132 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26132) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26132.1, data_15_26132.2]

/-- Complete interval computation for depth 15, residue 26133. -/
theorem bounds_15_26133 : exactInterval 15 26133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26133 : oddCount 26133 15 = 5 ∧ acceleratedOrbit 15 26133 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26133) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26133.1, data_15_26133.2]

/-- Complete interval computation for depth 15, residue 26134. -/
theorem bounds_15_26134 : exactInterval 15 26134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26134 : oddCount 26134 15 = 9 ∧ acceleratedOrbit 15 26134 = 15704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26134) = 3 ^ 9 * m + 15704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26134.1, data_15_26134.2]

/-- Complete interval computation for depth 15, residue 26135. -/
theorem bounds_15_26135 : exactInterval 15 26135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26135 : oddCount 26135 15 = 9 ∧ acceleratedOrbit 15 26135 = 15704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26135) = 3 ^ 9 * m + 15704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26135.1, data_15_26135.2]

/-- Complete interval computation for depth 15, residue 26136. -/
theorem bounds_15_26136 : exactInterval 15 26136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26136 : oddCount 26136 15 = 5 ∧ acceleratedOrbit 15 26136 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26136) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26136.1, data_15_26136.2]

/-- Complete interval computation for depth 15, residue 26137. -/
theorem bounds_15_26137 : exactInterval 15 26137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26137 : oddCount 26137 15 = 9 ∧ acceleratedOrbit 15 26137 = 15704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26137) = 3 ^ 9 * m + 15704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26137.1, data_15_26137.2]

/-- Complete interval computation for depth 15, residue 26138. -/
theorem bounds_15_26138 : exactInterval 15 26138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26138 : oddCount 26138 15 = 5 ∧ acceleratedOrbit 15 26138 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26138) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26138.1, data_15_26138.2]

/-- Complete interval computation for depth 15, residue 26139. -/
theorem bounds_15_26139 : exactInterval 15 26139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26139 : oddCount 26139 15 = 8 ∧ acceleratedOrbit 15 26139 = 5234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26139) = 3 ^ 8 * m + 5234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26139.1, data_15_26139.2]

/-- Complete interval computation for depth 15, residue 26140. -/
theorem bounds_15_26140 : exactInterval 15 26140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26140 : oddCount 26140 15 = 5 ∧ acceleratedOrbit 15 26140 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26140) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26140.1, data_15_26140.2]

/-- Complete interval computation for depth 15, residue 26141. -/
theorem bounds_15_26141 : exactInterval 15 26141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26141 : oddCount 26141 15 = 5 ∧ acceleratedOrbit 15 26141 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26141) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26141.1, data_15_26141.2]

/-- Complete interval computation for depth 15, residue 26142. -/
theorem bounds_15_26142 : exactInterval 15 26142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26142 : oddCount 26142 15 = 5 ∧ acceleratedOrbit 15 26142 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26142) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26142.1, data_15_26142.2]

/-- Complete interval computation for depth 15, residue 26143. -/
theorem bounds_15_26143 : exactInterval 15 26143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26143 : oddCount 26143 15 = 10 ∧ acceleratedOrbit 15 26143 = 47114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26143) = 3 ^ 10 * m + 47114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26143.1, data_15_26143.2]

/-- Complete interval computation for depth 15, residue 26144. -/
theorem bounds_15_26144 : exactInterval 15 26144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26144 : oddCount 26144 15 = 4 ∧ acceleratedOrbit 15 26144 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26144) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26144.1, data_15_26144.2]

/-- Complete interval computation for depth 15, residue 26145. -/
theorem bounds_15_26145 : exactInterval 15 26145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26145 : oddCount 26145 15 = 8 ∧ acceleratedOrbit 15 26145 = 5237 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26145) = 3 ^ 8 * m + 5237 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26145.1, data_15_26145.2]

/-- Complete interval computation for depth 15, residue 26146. -/
theorem bounds_15_26146 : exactInterval 15 26146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26146 : oddCount 26146 15 = 5 ∧ acceleratedOrbit 15 26146 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26146) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26146.1, data_15_26146.2]

/-- Complete interval computation for depth 15, residue 26147. -/
theorem bounds_15_26147 : exactInterval 15 26147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26147 : oddCount 26147 15 = 5 ∧ acceleratedOrbit 15 26147 = 194 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26147) = 3 ^ 5 * m + 194 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26147.1, data_15_26147.2]

end Collatz.Research.PassageAtlas.Batch0798
