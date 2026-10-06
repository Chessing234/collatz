import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0188

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6127. -/
theorem bounds_15_6127 : exactInterval 15 6127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6127 : oddCount 6127 15 = 7 ∧ acceleratedOrbit 15 6127 = 409 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6127) = 3 ^ 7 * m + 409 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6127.1, data_15_6127.2]

/-- Complete interval computation for depth 15, residue 6128. -/
theorem bounds_15_6128 : exactInterval 15 6128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6128 : oddCount 6128 15 = 7 ∧ acceleratedOrbit 15 6128 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6128) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6128.1, data_15_6128.2]

/-- Complete interval computation for depth 15, residue 6129. -/
theorem bounds_15_6129 : exactInterval 15 6129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6129 : oddCount 6129 15 = 7 ∧ acceleratedOrbit 15 6129 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6129) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6129.1, data_15_6129.2]

/-- Complete interval computation for depth 15, residue 6130. -/
theorem bounds_15_6130 : exactInterval 15 6130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6130 : oddCount 6130 15 = 10 ∧ acceleratedOrbit 15 6130 = 11056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6130) = 3 ^ 10 * m + 11056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6130.1, data_15_6130.2]

/-- Complete interval computation for depth 15, residue 6131. -/
theorem bounds_15_6131 : exactInterval 15 6131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6131 : oddCount 6131 15 = 10 ∧ acceleratedOrbit 15 6131 = 11056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6131) = 3 ^ 10 * m + 11056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6131.1, data_15_6131.2]

/-- Complete interval computation for depth 15, residue 6132. -/
theorem bounds_15_6132 : exactInterval 15 6132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6132 : oddCount 6132 15 = 7 ∧ acceleratedOrbit 15 6132 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6132) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6132.1, data_15_6132.2]

/-- Complete interval computation for depth 15, residue 6133. -/
theorem bounds_15_6133 : exactInterval 15 6133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6133 : oddCount 6133 15 = 7 ∧ acceleratedOrbit 15 6133 = 410 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6133) = 3 ^ 7 * m + 410 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6133.1, data_15_6133.2]

/-- Complete interval computation for depth 15, residue 6134. -/
theorem bounds_15_6134 : exactInterval 15 6134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6134 : oddCount 6134 15 = 8 ∧ acceleratedOrbit 15 6134 = 1229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6134) = 3 ^ 8 * m + 1229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6134.1, data_15_6134.2]

/-- Complete interval computation for depth 15, residue 6135. -/
theorem bounds_15_6135 : exactInterval 15 6135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6135 : oddCount 6135 15 = 8 ∧ acceleratedOrbit 15 6135 = 1229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6135) = 3 ^ 8 * m + 1229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6135.1, data_15_6135.2]

/-- Complete interval computation for depth 15, residue 6136. -/
theorem bounds_15_6136 : exactInterval 15 6136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6136 : oddCount 6136 15 = 10 ∧ acceleratedOrbit 15 6136 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6136) = 3 ^ 10 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6136.1, data_15_6136.2]

/-- Complete interval computation for depth 15, residue 6137. -/
theorem bounds_15_6137 : exactInterval 15 6137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6137 : oddCount 6137 15 = 9 ∧ acceleratedOrbit 15 6137 = 3689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6137) = 3 ^ 9 * m + 3689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6137.1, data_15_6137.2]

/-- Complete interval computation for depth 15, residue 6138. -/
theorem bounds_15_6138 : exactInterval 15 6138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6138 : oddCount 6138 15 = 10 ∧ acceleratedOrbit 15 6138 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6138) = 3 ^ 10 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6138.1, data_15_6138.2]

/-- Complete interval computation for depth 15, residue 6139. -/
theorem bounds_15_6139 : exactInterval 15 6139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6139 : oddCount 6139 15 = 11 ∧ acceleratedOrbit 15 6139 = 33200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6139) = 3 ^ 11 * m + 33200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6139.1, data_15_6139.2]

/-- Complete interval computation for depth 15, residue 6140. -/
theorem bounds_15_6140 : exactInterval 15 6140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6140 : oddCount 6140 15 = 10 ∧ acceleratedOrbit 15 6140 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6140) = 3 ^ 10 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6140.1, data_15_6140.2]

/-- Complete interval computation for depth 15, residue 6141. -/
theorem bounds_15_6141 : exactInterval 15 6141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6141 : oddCount 6141 15 = 10 ∧ acceleratedOrbit 15 6141 = 11072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6141) = 3 ^ 10 * m + 11072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6141.1, data_15_6141.2]

/-- Complete interval computation for depth 15, residue 6142. -/
theorem bounds_15_6142 : exactInterval 15 6142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6142 : oddCount 6142 15 = 11 ∧ acceleratedOrbit 15 6142 = 33215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6142) = 3 ^ 11 * m + 33215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6142.1, data_15_6142.2]

/-- Complete interval computation for depth 15, residue 6143. -/
theorem bounds_15_6143 : exactInterval 15 6143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6143 : oddCount 6143 15 = 11 ∧ acceleratedOrbit 15 6143 = 33215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6143) = 3 ^ 11 * m + 33215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6143.1, data_15_6143.2]

/-- Complete interval computation for depth 15, residue 6144. -/
theorem bounds_15_6144 : exactInterval 15 6144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6144 : oddCount 6144 15 = 2 ∧ acceleratedOrbit 15 6144 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6144) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6144.1, data_15_6144.2]

/-- Complete interval computation for depth 15, residue 6145. -/
theorem bounds_15_6145 : exactInterval 15 6145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6145 : oddCount 6145 15 = 8 ∧ acceleratedOrbit 15 6145 = 1232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6145) = 3 ^ 8 * m + 1232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6145.1, data_15_6145.2]

/-- Complete interval computation for depth 15, residue 6146. -/
theorem bounds_15_6146 : exactInterval 15 6146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6146 : oddCount 6146 15 = 6 ∧ acceleratedOrbit 15 6146 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6146) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6146.1, data_15_6146.2]

/-- Complete interval computation for depth 15, residue 6147. -/
theorem bounds_15_6147 : exactInterval 15 6147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6147 : oddCount 6147 15 = 6 ∧ acceleratedOrbit 15 6147 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6147) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6147.1, data_15_6147.2]

/-- Complete interval computation for depth 15, residue 6148. -/
theorem bounds_15_6148 : exactInterval 15 6148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6148 : oddCount 6148 15 = 8 ∧ acceleratedOrbit 15 6148 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6148) = 3 ^ 8 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6148.1, data_15_6148.2]

/-- Complete interval computation for depth 15, residue 6149. -/
theorem bounds_15_6149 : exactInterval 15 6149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6149 : oddCount 6149 15 = 8 ∧ acceleratedOrbit 15 6149 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6149) = 3 ^ 8 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6149.1, data_15_6149.2]

/-- Complete interval computation for depth 15, residue 6150. -/
theorem bounds_15_6150 : exactInterval 15 6150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6150 : oddCount 6150 15 = 8 ∧ acceleratedOrbit 15 6150 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6150) = 3 ^ 8 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6150.1, data_15_6150.2]

/-- Complete interval computation for depth 15, residue 6151. -/
theorem bounds_15_6151 : exactInterval 15 6151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6151 : oddCount 6151 15 = 6 ∧ acceleratedOrbit 15 6151 = 137 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6151) = 3 ^ 6 * m + 137 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6151.1, data_15_6151.2]

/-- Complete interval computation for depth 15, residue 6152. -/
theorem bounds_15_6152 : exactInterval 15 6152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6152 : oddCount 6152 15 = 5 ∧ acceleratedOrbit 15 6152 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6152) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6152.1, data_15_6152.2]

/-- Complete interval computation for depth 15, residue 6153. -/
theorem bounds_15_6153 : exactInterval 15 6153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6153 : oddCount 6153 15 = 10 ∧ acceleratedOrbit 15 6153 = 11096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6153) = 3 ^ 10 * m + 11096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6153.1, data_15_6153.2]

/-- Complete interval computation for depth 15, residue 6154. -/
theorem bounds_15_6154 : exactInterval 15 6154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6154 : oddCount 6154 15 = 5 ∧ acceleratedOrbit 15 6154 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6154) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6154.1, data_15_6154.2]

/-- Complete interval computation for depth 15, residue 6155. -/
theorem bounds_15_6155 : exactInterval 15 6155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6155 : oddCount 6155 15 = 8 ∧ acceleratedOrbit 15 6155 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6155) = 3 ^ 8 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6155.1, data_15_6155.2]

/-- Complete interval computation for depth 15, residue 6156. -/
theorem bounds_15_6156 : exactInterval 15 6156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6156 : oddCount 6156 15 = 5 ∧ acceleratedOrbit 15 6156 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6156) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6156.1, data_15_6156.2]

/-- Complete interval computation for depth 15, residue 6157. -/
theorem bounds_15_6157 : exactInterval 15 6157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6157 : oddCount 6157 15 = 5 ∧ acceleratedOrbit 15 6157 = 46 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6157) = 3 ^ 5 * m + 46 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6157.1, data_15_6157.2]

/-- Complete interval computation for depth 15, residue 6158. -/
theorem bounds_15_6158 : exactInterval 15 6158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6158 : oddCount 6158 15 = 8 ∧ acceleratedOrbit 15 6158 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6158) = 3 ^ 8 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6158.1, data_15_6158.2]

/-- Complete interval computation for depth 15, residue 6159. -/
theorem bounds_15_6159 : exactInterval 15 6159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6159 : oddCount 6159 15 = 8 ∧ acceleratedOrbit 15 6159 = 1235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6159) = 3 ^ 8 * m + 1235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6159.1, data_15_6159.2]

end Collatz.Research.PassageAtlas.Batch0188
