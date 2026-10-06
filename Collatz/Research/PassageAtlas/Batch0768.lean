import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0768

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25133. -/
theorem bounds_15_25133 : exactInterval 15 25133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25133 : oddCount 25133 15 = 8 ∧ acceleratedOrbit 15 25133 = 5035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25133) = 3 ^ 8 * m + 5035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25133.1, data_15_25133.2]

/-- Complete interval computation for depth 15, residue 25134. -/
theorem bounds_15_25134 : exactInterval 15 25134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25134 : oddCount 25134 15 = 8 ∧ acceleratedOrbit 15 25134 = 5035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25134) = 3 ^ 8 * m + 5035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25134.1, data_15_25134.2]

/-- Complete interval computation for depth 15, residue 25135. -/
theorem bounds_15_25135 : exactInterval 15 25135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25135 : oddCount 25135 15 = 12 ∧ acceleratedOrbit 15 25135 = 407672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25135) = 3 ^ 12 * m + 407672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25135.1, data_15_25135.2]

/-- Complete interval computation for depth 15, residue 25136. -/
theorem bounds_15_25136 : exactInterval 15 25136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25136 : oddCount 25136 15 = 5 ∧ acceleratedOrbit 15 25136 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25136) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25136.1, data_15_25136.2]

/-- Complete interval computation for depth 15, residue 25137. -/
theorem bounds_15_25137 : exactInterval 15 25137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25137 : oddCount 25137 15 = 8 ∧ acceleratedOrbit 15 25137 = 5035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25137) = 3 ^ 8 * m + 5035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25137.1, data_15_25137.2]

/-- Complete interval computation for depth 15, residue 25138. -/
theorem bounds_15_25138 : exactInterval 15 25138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25138 : oddCount 25138 15 = 8 ∧ acceleratedOrbit 15 25138 = 5035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25138) = 3 ^ 8 * m + 5035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25138.1, data_15_25138.2]

/-- Complete interval computation for depth 15, residue 25139. -/
theorem bounds_15_25139 : exactInterval 15 25139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25139 : oddCount 25139 15 = 8 ∧ acceleratedOrbit 15 25139 = 5035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25139) = 3 ^ 8 * m + 5035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25139.1, data_15_25139.2]

/-- Complete interval computation for depth 15, residue 25140. -/
theorem bounds_15_25140 : exactInterval 15 25140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25140 : oddCount 25140 15 = 5 ∧ acceleratedOrbit 15 25140 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25140) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25140.1, data_15_25140.2]

/-- Complete interval computation for depth 15, residue 25141. -/
theorem bounds_15_25141 : exactInterval 15 25141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25141 : oddCount 25141 15 = 5 ∧ acceleratedOrbit 15 25141 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25141) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25141.1, data_15_25141.2]

/-- Complete interval computation for depth 15, residue 25142. -/
theorem bounds_15_25142 : exactInterval 15 25142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25142 : oddCount 25142 15 = 9 ∧ acceleratedOrbit 15 25142 = 15104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25142) = 3 ^ 9 * m + 15104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25142.1, data_15_25142.2]

/-- Complete interval computation for depth 15, residue 25143. -/
theorem bounds_15_25143 : exactInterval 15 25143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25143 : oddCount 25143 15 = 9 ∧ acceleratedOrbit 15 25143 = 15104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25143) = 3 ^ 9 * m + 15104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25143.1, data_15_25143.2]

/-- Complete interval computation for depth 15, residue 25144. -/
theorem bounds_15_25144 : exactInterval 15 25144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25144 : oddCount 25144 15 = 7 ∧ acceleratedOrbit 15 25144 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25144) = 3 ^ 7 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25144.1, data_15_25144.2]

/-- Complete interval computation for depth 15, residue 25145. -/
theorem bounds_15_25145 : exactInterval 15 25145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25145 : oddCount 25145 15 = 10 ∧ acceleratedOrbit 15 25145 = 45319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25145) = 3 ^ 10 * m + 45319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25145.1, data_15_25145.2]

/-- Complete interval computation for depth 15, residue 25146. -/
theorem bounds_15_25146 : exactInterval 15 25146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25146 : oddCount 25146 15 = 7 ∧ acceleratedOrbit 15 25146 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25146) = 3 ^ 7 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25146.1, data_15_25146.2]

/-- Complete interval computation for depth 15, residue 25147. -/
theorem bounds_15_25147 : exactInterval 15 25147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25147 : oddCount 25147 15 = 6 ∧ acceleratedOrbit 15 25147 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25147) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25147.1, data_15_25147.2]

/-- Complete interval computation for depth 15, residue 25148. -/
theorem bounds_15_25148 : exactInterval 15 25148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25148 : oddCount 25148 15 = 7 ∧ acceleratedOrbit 15 25148 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25148) = 3 ^ 7 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25148.1, data_15_25148.2]

/-- Complete interval computation for depth 15, residue 25149. -/
theorem bounds_15_25149 : exactInterval 15 25149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25149 : oddCount 25149 15 = 7 ∧ acceleratedOrbit 15 25149 = 1679 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25149) = 3 ^ 7 * m + 1679 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25149.1, data_15_25149.2]

/-- Complete interval computation for depth 15, residue 25150. -/
theorem bounds_15_25150 : exactInterval 15 25150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25150 : oddCount 25150 15 = 9 ∧ acceleratedOrbit 15 25150 = 15110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25150) = 3 ^ 9 * m + 15110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25150.1, data_15_25150.2]

/-- Complete interval computation for depth 15, residue 25151. -/
theorem bounds_15_25151 : exactInterval 15 25151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25151 : oddCount 25151 15 = 9 ∧ acceleratedOrbit 15 25151 = 15110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25151) = 3 ^ 9 * m + 15110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25151.1, data_15_25151.2]

/-- Complete interval computation for depth 15, residue 25152. -/
theorem bounds_15_25152 : exactInterval 15 25152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25152 : oddCount 25152 15 = 6 ∧ acceleratedOrbit 15 25152 = 562 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25152) = 3 ^ 6 * m + 562 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25152.1, data_15_25152.2]

/-- Complete interval computation for depth 15, residue 25153. -/
theorem bounds_15_25153 : exactInterval 15 25153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25153 : oddCount 25153 15 = 6 ∧ acceleratedOrbit 15 25153 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25153) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25153.1, data_15_25153.2]

/-- Complete interval computation for depth 15, residue 25154. -/
theorem bounds_15_25154 : exactInterval 15 25154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25154 : oddCount 25154 15 = 6 ∧ acceleratedOrbit 15 25154 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25154) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25154.1, data_15_25154.2]

/-- Complete interval computation for depth 15, residue 25155. -/
theorem bounds_15_25155 : exactInterval 15 25155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25155 : oddCount 25155 15 = 6 ∧ acceleratedOrbit 15 25155 = 560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25155) = 3 ^ 6 * m + 560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25155.1, data_15_25155.2]

/-- Complete interval computation for depth 15, residue 25156. -/
theorem bounds_15_25156 : exactInterval 15 25156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25156 : oddCount 25156 15 = 8 ∧ acceleratedOrbit 15 25156 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25156) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25156.1, data_15_25156.2]

/-- Complete interval computation for depth 15, residue 25157. -/
theorem bounds_15_25157 : exactInterval 15 25157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25157 : oddCount 25157 15 = 8 ∧ acceleratedOrbit 15 25157 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25157) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25157.1, data_15_25157.2]

/-- Complete interval computation for depth 15, residue 25158. -/
theorem bounds_15_25158 : exactInterval 15 25158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25158 : oddCount 25158 15 = 8 ∧ acceleratedOrbit 15 25158 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25158) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25158.1, data_15_25158.2]

/-- Complete interval computation for depth 15, residue 25159. -/
theorem bounds_15_25159 : exactInterval 15 25159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25159 : oddCount 25159 15 = 8 ∧ acceleratedOrbit 15 25159 = 5039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25159) = 3 ^ 8 * m + 5039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25159.1, data_15_25159.2]

/-- Complete interval computation for depth 15, residue 25160. -/
theorem bounds_15_25160 : exactInterval 15 25160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25160 : oddCount 25160 15 = 8 ∧ acceleratedOrbit 15 25160 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25160) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25160.1, data_15_25160.2]

/-- Complete interval computation for depth 15, residue 25161. -/
theorem bounds_15_25161 : exactInterval 15 25161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25161 : oddCount 25161 15 = 8 ∧ acceleratedOrbit 15 25161 = 5039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25161) = 3 ^ 8 * m + 5039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25161.1, data_15_25161.2]

/-- Complete interval computation for depth 15, residue 25162. -/
theorem bounds_15_25162 : exactInterval 15 25162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25162 : oddCount 25162 15 = 8 ∧ acceleratedOrbit 15 25162 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25162) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25162.1, data_15_25162.2]

/-- Complete interval computation for depth 15, residue 25163. -/
theorem bounds_15_25163 : exactInterval 15 25163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25163 : oddCount 25163 15 = 8 ∧ acceleratedOrbit 15 25163 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25163) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25163.1, data_15_25163.2]

/-- Complete interval computation for depth 15, residue 25164. -/
theorem bounds_15_25164 : exactInterval 15 25164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25164 : oddCount 25164 15 = 8 ∧ acceleratedOrbit 15 25164 = 5042 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25164) = 3 ^ 8 * m + 5042 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25164.1, data_15_25164.2]

end Collatz.Research.PassageAtlas.Batch0768
