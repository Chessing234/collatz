import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0951

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31129. -/
theorem bounds_15_31129 : exactInterval 15 31129 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31129 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31129) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31129 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31129 : oddCount 31129 15 = 8 ∧ acceleratedOrbit 15 31129 = 6236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31129 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31129) = 3 ^ 8 * m + 6236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31129.1, data_15_31129.2]

/-- Complete interval computation for depth 15, residue 31130. -/
theorem bounds_15_31130 : exactInterval 15 31130 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31130 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31130) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31130 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31130 : oddCount 31130 15 = 4 ∧ acceleratedOrbit 15 31130 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31130 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31130) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31130.1, data_15_31130.2]

/-- Complete interval computation for depth 15, residue 31131. -/
theorem bounds_15_31131 : exactInterval 15 31131 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31131 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31131) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31131 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31131 : oddCount 31131 15 = 11 ∧ acceleratedOrbit 15 31131 = 168308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31131 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31131) = 3 ^ 11 * m + 168308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31131.1, data_15_31131.2]

/-- Complete interval computation for depth 15, residue 31132. -/
theorem bounds_15_31132 : exactInterval 15 31132 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31132 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31132) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31132 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31132 : oddCount 31132 15 = 9 ∧ acceleratedOrbit 15 31132 = 18704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31132 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31132) = 3 ^ 9 * m + 18704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31132.1, data_15_31132.2]

/-- Complete interval computation for depth 15, residue 31133. -/
theorem bounds_15_31133 : exactInterval 15 31133 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31133 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31133) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31133 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31133 : oddCount 31133 15 = 9 ∧ acceleratedOrbit 15 31133 = 18704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31133 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31133) = 3 ^ 9 * m + 18704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31133.1, data_15_31133.2]

/-- Complete interval computation for depth 15, residue 31134. -/
theorem bounds_15_31134 : exactInterval 15 31134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31134 : oddCount 31134 15 = 9 ∧ acceleratedOrbit 15 31134 = 18704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31134) = 3 ^ 9 * m + 18704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31134.1, data_15_31134.2]

/-- Complete interval computation for depth 15, residue 31135. -/
theorem bounds_15_31135 : exactInterval 15 31135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31135 : oddCount 31135 15 = 9 ∧ acceleratedOrbit 15 31135 = 18703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31135) = 3 ^ 9 * m + 18703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31135.1, data_15_31135.2]

/-- Complete interval computation for depth 15, residue 31136. -/
theorem bounds_15_31136 : exactInterval 15 31136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31136 : oddCount 31136 15 = 5 ∧ acceleratedOrbit 15 31136 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31136) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31136.1, data_15_31136.2]

/-- Complete interval computation for depth 15, residue 31137. -/
theorem bounds_15_31137 : exactInterval 15 31137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31137 : oddCount 31137 15 = 9 ∧ acceleratedOrbit 15 31137 = 18706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31137) = 3 ^ 9 * m + 18706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31137.1, data_15_31137.2]

/-- Complete interval computation for depth 15, residue 31138. -/
theorem bounds_15_31138 : exactInterval 15 31138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31138 : oddCount 31138 15 = 10 ∧ acceleratedOrbit 15 31138 = 56132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31138) = 3 ^ 10 * m + 56132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31138.1, data_15_31138.2]

/-- Complete interval computation for depth 15, residue 31139. -/
theorem bounds_15_31139 : exactInterval 15 31139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31139 : oddCount 31139 15 = 10 ∧ acceleratedOrbit 15 31139 = 56132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31139) = 3 ^ 10 * m + 56132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31139.1, data_15_31139.2]

/-- Complete interval computation for depth 15, residue 31140. -/
theorem bounds_15_31140 : exactInterval 15 31140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31140 : oddCount 31140 15 = 10 ∧ acceleratedOrbit 15 31140 = 56132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31140) = 3 ^ 10 * m + 56132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31140.1, data_15_31140.2]

/-- Complete interval computation for depth 15, residue 31141. -/
theorem bounds_15_31141 : exactInterval 15 31141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31141 : oddCount 31141 15 = 10 ∧ acceleratedOrbit 15 31141 = 56132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31141) = 3 ^ 10 * m + 56132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31141.1, data_15_31141.2]

/-- Complete interval computation for depth 15, residue 31142. -/
theorem bounds_15_31142 : exactInterval 15 31142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31142 : oddCount 31142 15 = 10 ∧ acceleratedOrbit 15 31142 = 56132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31142) = 3 ^ 10 * m + 56132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31142.1, data_15_31142.2]

/-- Complete interval computation for depth 15, residue 31143. -/
theorem bounds_15_31143 : exactInterval 15 31143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31143 : oddCount 31143 15 = 9 ∧ acceleratedOrbit 15 31143 = 18710 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31143) = 3 ^ 9 * m + 18710 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31143.1, data_15_31143.2]

/-- Complete interval computation for depth 15, residue 31144. -/
theorem bounds_15_31144 : exactInterval 15 31144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31144 : oddCount 31144 15 = 5 ∧ acceleratedOrbit 15 31144 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31144) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31144.1, data_15_31144.2]

/-- Complete interval computation for depth 15, residue 31145. -/
theorem bounds_15_31145 : exactInterval 15 31145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31145 : oddCount 31145 15 = 10 ∧ acceleratedOrbit 15 31145 = 56128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31145) = 3 ^ 10 * m + 56128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31145.1, data_15_31145.2]

/-- Complete interval computation for depth 15, residue 31146. -/
theorem bounds_15_31146 : exactInterval 15 31146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31146 : oddCount 31146 15 = 5 ∧ acceleratedOrbit 15 31146 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31146) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31146.1, data_15_31146.2]

/-- Complete interval computation for depth 15, residue 31147. -/
theorem bounds_15_31147 : exactInterval 15 31147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31147 : oddCount 31147 15 = 12 ∧ acceleratedOrbit 15 31147 = 505196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31147) = 3 ^ 12 * m + 505196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31147.1, data_15_31147.2]

/-- Complete interval computation for depth 15, residue 31148. -/
theorem bounds_15_31148 : exactInterval 15 31148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31148 : oddCount 31148 15 = 8 ∧ acceleratedOrbit 15 31148 = 6239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31148) = 3 ^ 8 * m + 6239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31148.1, data_15_31148.2]

/-- Complete interval computation for depth 15, residue 31149. -/
theorem bounds_15_31149 : exactInterval 15 31149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31149 : oddCount 31149 15 = 8 ∧ acceleratedOrbit 15 31149 = 6239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31149) = 3 ^ 8 * m + 6239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31149.1, data_15_31149.2]

/-- Complete interval computation for depth 15, residue 31150. -/
theorem bounds_15_31150 : exactInterval 15 31150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31150 : oddCount 31150 15 = 8 ∧ acceleratedOrbit 15 31150 = 6239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31150) = 3 ^ 8 * m + 6239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31150.1, data_15_31150.2]

/-- Complete interval computation for depth 15, residue 31151. -/
theorem bounds_15_31151 : exactInterval 15 31151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31151 : oddCount 31151 15 = 8 ∧ acceleratedOrbit 15 31151 = 6238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31151) = 3 ^ 8 * m + 6238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31151.1, data_15_31151.2]

/-- Complete interval computation for depth 15, residue 31152. -/
theorem bounds_15_31152 : exactInterval 15 31152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31152 : oddCount 31152 15 = 7 ∧ acceleratedOrbit 15 31152 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31152) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31152.1, data_15_31152.2]

/-- Complete interval computation for depth 15, residue 31153. -/
theorem bounds_15_31153 : exactInterval 15 31153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31153 : oddCount 31153 15 = 7 ∧ acceleratedOrbit 15 31153 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31153) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31153.1, data_15_31153.2]

/-- Complete interval computation for depth 15, residue 31154. -/
theorem bounds_15_31154 : exactInterval 15 31154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31154 : oddCount 31154 15 = 7 ∧ acceleratedOrbit 15 31154 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31154) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31154.1, data_15_31154.2]

/-- Complete interval computation for depth 15, residue 31155. -/
theorem bounds_15_31155 : exactInterval 15 31155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31155 : oddCount 31155 15 = 7 ∧ acceleratedOrbit 15 31155 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31155) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31155.1, data_15_31155.2]

/-- Complete interval computation for depth 15, residue 31156. -/
theorem bounds_15_31156 : exactInterval 15 31156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31156 : oddCount 31156 15 = 7 ∧ acceleratedOrbit 15 31156 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31156) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31156.1, data_15_31156.2]

/-- Complete interval computation for depth 15, residue 31157. -/
theorem bounds_15_31157 : exactInterval 15 31157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31157 : oddCount 31157 15 = 7 ∧ acceleratedOrbit 15 31157 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31157) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31157.1, data_15_31157.2]

/-- Complete interval computation for depth 15, residue 31158. -/
theorem bounds_15_31158 : exactInterval 15 31158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31158 : oddCount 31158 15 = 7 ∧ acceleratedOrbit 15 31158 = 2080 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31158) = 3 ^ 7 * m + 2080 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31158.1, data_15_31158.2]

/-- Complete interval computation for depth 15, residue 31159. -/
theorem bounds_15_31159 : exactInterval 15 31159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31159 : oddCount 31159 15 = 7 ∧ acceleratedOrbit 15 31159 = 2080 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31159) = 3 ^ 7 * m + 2080 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31159.1, data_15_31159.2]

/-- Complete interval computation for depth 15, residue 31160. -/
theorem bounds_15_31160 : exactInterval 15 31160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31160 : oddCount 31160 15 = 7 ∧ acceleratedOrbit 15 31160 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31160) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31160.1, data_15_31160.2]

/-- Complete interval computation for depth 15, residue 31161. -/
theorem bounds_15_31161 : exactInterval 15 31161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31161 : oddCount 31161 15 = 7 ∧ acceleratedOrbit 15 31161 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31161) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31161.1, data_15_31161.2]

end Collatz.Research.PassageAtlas.Batch0951
