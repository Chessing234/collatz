import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0707

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23134. -/
theorem bounds_15_23134 : exactInterval 15 23134 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23134 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23134) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23134 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23134 : oddCount 23134 15 = 9 ∧ acceleratedOrbit 15 23134 = 13898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23134 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23134) = 3 ^ 9 * m + 13898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23134.1, data_15_23134.2]

/-- Complete interval computation for depth 15, residue 23135. -/
theorem bounds_15_23135 : exactInterval 15 23135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23135 : oddCount 23135 15 = 9 ∧ acceleratedOrbit 15 23135 = 13898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23135) = 3 ^ 9 * m + 13898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23135.1, data_15_23135.2]

/-- Complete interval computation for depth 15, residue 23136. -/
theorem bounds_15_23136 : exactInterval 15 23136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23136 : oddCount 23136 15 = 5 ∧ acceleratedOrbit 15 23136 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23136) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23136.1, data_15_23136.2]

/-- Complete interval computation for depth 15, residue 23137. -/
theorem bounds_15_23137 : exactInterval 15 23137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23137 : oddCount 23137 15 = 8 ∧ acceleratedOrbit 15 23137 = 4634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23137) = 3 ^ 8 * m + 4634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23137.1, data_15_23137.2]

/-- Complete interval computation for depth 15, residue 23138. -/
theorem bounds_15_23138 : exactInterval 15 23138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23138 : oddCount 23138 15 = 8 ∧ acceleratedOrbit 15 23138 = 4637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23138) = 3 ^ 8 * m + 4637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23138.1, data_15_23138.2]

/-- Complete interval computation for depth 15, residue 23139. -/
theorem bounds_15_23139 : exactInterval 15 23139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23139 : oddCount 23139 15 = 8 ∧ acceleratedOrbit 15 23139 = 4637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23139) = 3 ^ 8 * m + 4637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23139.1, data_15_23139.2]

/-- Complete interval computation for depth 15, residue 23140. -/
theorem bounds_15_23140 : exactInterval 15 23140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23140 : oddCount 23140 15 = 8 ∧ acceleratedOrbit 15 23140 = 4637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23140) = 3 ^ 8 * m + 4637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23140.1, data_15_23140.2]

/-- Complete interval computation for depth 15, residue 23141. -/
theorem bounds_15_23141 : exactInterval 15 23141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23141 : oddCount 23141 15 = 8 ∧ acceleratedOrbit 15 23141 = 4637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23141) = 3 ^ 8 * m + 4637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23141.1, data_15_23141.2]

/-- Complete interval computation for depth 15, residue 23142. -/
theorem bounds_15_23142 : exactInterval 15 23142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23142 : oddCount 23142 15 = 8 ∧ acceleratedOrbit 15 23142 = 4637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23142) = 3 ^ 8 * m + 4637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23142.1, data_15_23142.2]

/-- Complete interval computation for depth 15, residue 23143. -/
theorem bounds_15_23143 : exactInterval 15 23143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23143 : oddCount 23143 15 = 10 ∧ acceleratedOrbit 15 23143 = 41708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23143) = 3 ^ 10 * m + 41708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23143.1, data_15_23143.2]

/-- Complete interval computation for depth 15, residue 23144. -/
theorem bounds_15_23144 : exactInterval 15 23144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23144 : oddCount 23144 15 = 5 ∧ acceleratedOrbit 15 23144 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23144) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23144.1, data_15_23144.2]

/-- Complete interval computation for depth 15, residue 23145. -/
theorem bounds_15_23145 : exactInterval 15 23145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23145 : oddCount 23145 15 = 10 ∧ acceleratedOrbit 15 23145 = 41714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23145) = 3 ^ 10 * m + 41714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23145.1, data_15_23145.2]

/-- Complete interval computation for depth 15, residue 23146. -/
theorem bounds_15_23146 : exactInterval 15 23146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23146 : oddCount 23146 15 = 5 ∧ acceleratedOrbit 15 23146 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23146) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23146.1, data_15_23146.2]

/-- Complete interval computation for depth 15, residue 23147. -/
theorem bounds_15_23147 : exactInterval 15 23147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23147 : oddCount 23147 15 = 6 ∧ acceleratedOrbit 15 23147 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23147) = 3 ^ 6 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23147.1, data_15_23147.2]

/-- Complete interval computation for depth 15, residue 23148. -/
theorem bounds_15_23148 : exactInterval 15 23148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23148 : oddCount 23148 15 = 8 ∧ acceleratedOrbit 15 23148 = 4636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23148) = 3 ^ 8 * m + 4636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23148.1, data_15_23148.2]

/-- Complete interval computation for depth 15, residue 23149. -/
theorem bounds_15_23149 : exactInterval 15 23149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23149 : oddCount 23149 15 = 8 ∧ acceleratedOrbit 15 23149 = 4636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23149) = 3 ^ 8 * m + 4636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23149.1, data_15_23149.2]

/-- Complete interval computation for depth 15, residue 23150. -/
theorem bounds_15_23150 : exactInterval 15 23150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23150 : oddCount 23150 15 = 8 ∧ acceleratedOrbit 15 23150 = 4636 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23150) = 3 ^ 8 * m + 4636 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23150.1, data_15_23150.2]

/-- Complete interval computation for depth 15, residue 23151. -/
theorem bounds_15_23151 : exactInterval 15 23151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23151 : oddCount 23151 15 = 11 ∧ acceleratedOrbit 15 23151 = 125165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23151) = 3 ^ 11 * m + 125165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23151.1, data_15_23151.2]

/-- Complete interval computation for depth 15, residue 23152. -/
theorem bounds_15_23152 : exactInterval 15 23152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23152 : oddCount 23152 15 = 7 ∧ acceleratedOrbit 15 23152 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23152) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23152.1, data_15_23152.2]

/-- Complete interval computation for depth 15, residue 23153. -/
theorem bounds_15_23153 : exactInterval 15 23153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23153 : oddCount 23153 15 = 5 ∧ acceleratedOrbit 15 23153 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23153) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23153.1, data_15_23153.2]

/-- Complete interval computation for depth 15, residue 23154. -/
theorem bounds_15_23154 : exactInterval 15 23154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23154 : oddCount 23154 15 = 10 ∧ acceleratedOrbit 15 23154 = 41735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23154) = 3 ^ 10 * m + 41735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23154.1, data_15_23154.2]

/-- Complete interval computation for depth 15, residue 23155. -/
theorem bounds_15_23155 : exactInterval 15 23155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23155 : oddCount 23155 15 = 10 ∧ acceleratedOrbit 15 23155 = 41735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23155) = 3 ^ 10 * m + 41735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23155.1, data_15_23155.2]

/-- Complete interval computation for depth 15, residue 23156. -/
theorem bounds_15_23156 : exactInterval 15 23156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23156 : oddCount 23156 15 = 7 ∧ acceleratedOrbit 15 23156 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23156) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23156.1, data_15_23156.2]

/-- Complete interval computation for depth 15, residue 23157. -/
theorem bounds_15_23157 : exactInterval 15 23157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23157 : oddCount 23157 15 = 7 ∧ acceleratedOrbit 15 23157 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23157) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23157.1, data_15_23157.2]

/-- Complete interval computation for depth 15, residue 23158. -/
theorem bounds_15_23158 : exactInterval 15 23158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23158 : oddCount 23158 15 = 5 ∧ acceleratedOrbit 15 23158 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23158) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23158.1, data_15_23158.2]

/-- Complete interval computation for depth 15, residue 23159. -/
theorem bounds_15_23159 : exactInterval 15 23159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23159 : oddCount 23159 15 = 5 ∧ acceleratedOrbit 15 23159 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23159) = 3 ^ 5 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23159.1, data_15_23159.2]

/-- Complete interval computation for depth 15, residue 23160. -/
theorem bounds_15_23160 : exactInterval 15 23160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23160 : oddCount 23160 15 = 7 ∧ acceleratedOrbit 15 23160 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23160) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23160.1, data_15_23160.2]

/-- Complete interval computation for depth 15, residue 23161. -/
theorem bounds_15_23161 : exactInterval 15 23161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23161 : oddCount 23161 15 = 7 ∧ acceleratedOrbit 15 23161 = 1546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23161) = 3 ^ 7 * m + 1546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23161.1, data_15_23161.2]

/-- Complete interval computation for depth 15, residue 23162. -/
theorem bounds_15_23162 : exactInterval 15 23162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23162 : oddCount 23162 15 = 7 ∧ acceleratedOrbit 15 23162 = 1547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23162) = 3 ^ 7 * m + 1547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23162.1, data_15_23162.2]

/-- Complete interval computation for depth 15, residue 23163. -/
theorem bounds_15_23163 : exactInterval 15 23163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23163 : oddCount 23163 15 = 8 ∧ acceleratedOrbit 15 23163 = 4639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23163) = 3 ^ 8 * m + 4639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23163.1, data_15_23163.2]

/-- Complete interval computation for depth 15, residue 23164. -/
theorem bounds_15_23164 : exactInterval 15 23164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23164 : oddCount 23164 15 = 11 ∧ acceleratedOrbit 15 23164 = 125252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23164) = 3 ^ 11 * m + 125252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23164.1, data_15_23164.2]

/-- Complete interval computation for depth 15, residue 23165. -/
theorem bounds_15_23165 : exactInterval 15 23165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23165 : oddCount 23165 15 = 11 ∧ acceleratedOrbit 15 23165 = 125252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23165) = 3 ^ 11 * m + 125252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23165.1, data_15_23165.2]

end Collatz.Research.PassageAtlas.Batch0707
