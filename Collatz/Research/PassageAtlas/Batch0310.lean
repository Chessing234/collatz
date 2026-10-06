import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0310

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10125. -/
theorem bounds_15_10125 : exactInterval 15 10125 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10125 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10125) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10125 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10125 : oddCount 10125 15 = 5 ∧ acceleratedOrbit 15 10125 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10125 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10125) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10125.1, data_15_10125.2]

/-- Complete interval computation for depth 15, residue 10126. -/
theorem bounds_15_10126 : exactInterval 15 10126 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10126 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10126) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10126 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10126 : oddCount 10126 15 = 9 ∧ acceleratedOrbit 15 10126 = 6085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10126 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10126) = 3 ^ 9 * m + 6085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10126.1, data_15_10126.2]

/-- Complete interval computation for depth 15, residue 10127. -/
theorem bounds_15_10127 : exactInterval 15 10127 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10127 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10127) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10127 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10127 : oddCount 10127 15 = 9 ∧ acceleratedOrbit 15 10127 = 6085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10127 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10127) = 3 ^ 9 * m + 6085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10127.1, data_15_10127.2]

/-- Complete interval computation for depth 15, residue 10128. -/
theorem bounds_15_10128 : exactInterval 15 10128 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10128 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10128) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10128 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10128 : oddCount 10128 15 = 6 ∧ acceleratedOrbit 15 10128 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10128 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10128) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10128.1, data_15_10128.2]

/-- Complete interval computation for depth 15, residue 10129. -/
theorem bounds_15_10129 : exactInterval 15 10129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10129 : oddCount 10129 15 = 7 ∧ acceleratedOrbit 15 10129 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10129) = 3 ^ 7 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10129.1, data_15_10129.2]

/-- Complete interval computation for depth 15, residue 10130. -/
theorem bounds_15_10130 : exactInterval 15 10130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10130 : oddCount 10130 15 = 7 ∧ acceleratedOrbit 15 10130 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10130) = 3 ^ 7 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10130.1, data_15_10130.2]

/-- Complete interval computation for depth 15, residue 10131. -/
theorem bounds_15_10131 : exactInterval 15 10131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10131 : oddCount 10131 15 = 7 ∧ acceleratedOrbit 15 10131 = 677 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10131) = 3 ^ 7 * m + 677 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10131.1, data_15_10131.2]

/-- Complete interval computation for depth 15, residue 10132. -/
theorem bounds_15_10132 : exactInterval 15 10132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10132 : oddCount 10132 15 = 6 ∧ acceleratedOrbit 15 10132 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10132) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10132.1, data_15_10132.2]

/-- Complete interval computation for depth 15, residue 10133. -/
theorem bounds_15_10133 : exactInterval 15 10133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10133 : oddCount 10133 15 = 6 ∧ acceleratedOrbit 15 10133 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10133) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10133.1, data_15_10133.2]

/-- Complete interval computation for depth 15, residue 10134. -/
theorem bounds_15_10134 : exactInterval 15 10134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10134 : oddCount 10134 15 = 6 ∧ acceleratedOrbit 15 10134 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10134) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10134.1, data_15_10134.2]

/-- Complete interval computation for depth 15, residue 10135. -/
theorem bounds_15_10135 : exactInterval 15 10135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10135 : oddCount 10135 15 = 6 ∧ acceleratedOrbit 15 10135 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10135) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10135.1, data_15_10135.2]

/-- Complete interval computation for depth 15, residue 10136. -/
theorem bounds_15_10136 : exactInterval 15 10136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10136 : oddCount 10136 15 = 6 ∧ acceleratedOrbit 15 10136 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10136) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10136.1, data_15_10136.2]

/-- Complete interval computation for depth 15, residue 10137. -/
theorem bounds_15_10137 : exactInterval 15 10137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10137 : oddCount 10137 15 = 6 ∧ acceleratedOrbit 15 10137 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10137) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10137.1, data_15_10137.2]

/-- Complete interval computation for depth 15, residue 10138. -/
theorem bounds_15_10138 : exactInterval 15 10138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10138 : oddCount 10138 15 = 6 ∧ acceleratedOrbit 15 10138 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10138) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10138.1, data_15_10138.2]

/-- Complete interval computation for depth 15, residue 10139. -/
theorem bounds_15_10139 : exactInterval 15 10139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10139 : oddCount 10139 15 = 9 ∧ acceleratedOrbit 15 10139 = 6092 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10139) = 3 ^ 9 * m + 6092 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10139.1, data_15_10139.2]

/-- Complete interval computation for depth 15, residue 10140. -/
theorem bounds_15_10140 : exactInterval 15 10140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10140 : oddCount 10140 15 = 9 ∧ acceleratedOrbit 15 10140 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10140) = 3 ^ 9 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10140.1, data_15_10140.2]

/-- Complete interval computation for depth 15, residue 10141. -/
theorem bounds_15_10141 : exactInterval 15 10141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10141 : oddCount 10141 15 = 9 ∧ acceleratedOrbit 15 10141 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10141) = 3 ^ 9 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10141.1, data_15_10141.2]

/-- Complete interval computation for depth 15, residue 10142. -/
theorem bounds_15_10142 : exactInterval 15 10142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10142 : oddCount 10142 15 = 9 ∧ acceleratedOrbit 15 10142 = 6095 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10142) = 3 ^ 9 * m + 6095 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10142.1, data_15_10142.2]

/-- Complete interval computation for depth 15, residue 10143. -/
theorem bounds_15_10143 : exactInterval 15 10143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10143 : oddCount 10143 15 = 10 ∧ acceleratedOrbit 15 10143 = 18281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10143) = 3 ^ 10 * m + 18281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10143.1, data_15_10143.2]

/-- Complete interval computation for depth 15, residue 10144. -/
theorem bounds_15_10144 : exactInterval 15 10144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10144 : oddCount 10144 15 = 5 ∧ acceleratedOrbit 15 10144 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10144) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10144.1, data_15_10144.2]

/-- Complete interval computation for depth 15, residue 10145. -/
theorem bounds_15_10145 : exactInterval 15 10145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10145 : oddCount 10145 15 = 6 ∧ acceleratedOrbit 15 10145 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10145) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10145.1, data_15_10145.2]

/-- Complete interval computation for depth 15, residue 10146. -/
theorem bounds_15_10146 : exactInterval 15 10146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10146 : oddCount 10146 15 = 6 ∧ acceleratedOrbit 15 10146 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10146) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10146.1, data_15_10146.2]

/-- Complete interval computation for depth 15, residue 10147. -/
theorem bounds_15_10147 : exactInterval 15 10147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10147 : oddCount 10147 15 = 6 ∧ acceleratedOrbit 15 10147 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10147) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10147.1, data_15_10147.2]

/-- Complete interval computation for depth 15, residue 10148. -/
theorem bounds_15_10148 : exactInterval 15 10148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10148 : oddCount 10148 15 = 9 ∧ acceleratedOrbit 15 10148 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10148) = 3 ^ 9 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10148.1, data_15_10148.2]

/-- Complete interval computation for depth 15, residue 10149. -/
theorem bounds_15_10149 : exactInterval 15 10149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10149 : oddCount 10149 15 = 9 ∧ acceleratedOrbit 15 10149 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10149) = 3 ^ 9 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10149.1, data_15_10149.2]

/-- Complete interval computation for depth 15, residue 10150. -/
theorem bounds_15_10150 : exactInterval 15 10150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10150 : oddCount 10150 15 = 9 ∧ acceleratedOrbit 15 10150 = 6101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10150) = 3 ^ 9 * m + 6101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10150.1, data_15_10150.2]

/-- Complete interval computation for depth 15, residue 10151. -/
theorem bounds_15_10151 : exactInterval 15 10151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10151 : oddCount 10151 15 = 10 ∧ acceleratedOrbit 15 10151 = 18296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10151) = 3 ^ 10 * m + 18296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10151.1, data_15_10151.2]

/-- Complete interval computation for depth 15, residue 10152. -/
theorem bounds_15_10152 : exactInterval 15 10152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10152 : oddCount 10152 15 = 5 ∧ acceleratedOrbit 15 10152 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10152) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10152.1, data_15_10152.2]

/-- Complete interval computation for depth 15, residue 10153. -/
theorem bounds_15_10153 : exactInterval 15 10153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10153 : oddCount 10153 15 = 12 ∧ acceleratedOrbit 15 10153 = 164693 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10153) = 3 ^ 12 * m + 164693 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10153.1, data_15_10153.2]

/-- Complete interval computation for depth 15, residue 10154. -/
theorem bounds_15_10154 : exactInterval 15 10154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10154 : oddCount 10154 15 = 5 ∧ acceleratedOrbit 15 10154 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10154) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10154.1, data_15_10154.2]

/-- Complete interval computation for depth 15, residue 10155. -/
theorem bounds_15_10155 : exactInterval 15 10155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10155 : oddCount 10155 15 = 11 ∧ acceleratedOrbit 15 10155 = 54917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10155) = 3 ^ 11 * m + 54917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10155.1, data_15_10155.2]

/-- Complete interval computation for depth 15, residue 10156. -/
theorem bounds_15_10156 : exactInterval 15 10156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10156 : oddCount 10156 15 = 8 ∧ acceleratedOrbit 15 10156 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10156) = 3 ^ 8 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10156.1, data_15_10156.2]

/-- Complete interval computation for depth 15, residue 10157. -/
theorem bounds_15_10157 : exactInterval 15 10157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10157 : oddCount 10157 15 = 8 ∧ acceleratedOrbit 15 10157 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10157) = 3 ^ 8 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10157.1, data_15_10157.2]

end Collatz.Research.PassageAtlas.Batch0310
