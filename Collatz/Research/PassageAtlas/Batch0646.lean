import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0646

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21135. -/
theorem bounds_15_21135 : exactInterval 15 21135 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21135 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21135) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21135 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21135 : oddCount 21135 15 = 10 ∧ acceleratedOrbit 15 21135 = 38090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21135 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21135) = 3 ^ 10 * m + 38090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21135.1, data_15_21135.2]

/-- Complete interval computation for depth 15, residue 21136. -/
theorem bounds_15_21136 : exactInterval 15 21136 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21136 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21136) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21136 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21136 : oddCount 21136 15 = 8 ∧ acceleratedOrbit 15 21136 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21136 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21136) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21136.1, data_15_21136.2]

/-- Complete interval computation for depth 15, residue 21137. -/
theorem bounds_15_21137 : exactInterval 15 21137 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21137 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21137) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21137 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21137 : oddCount 21137 15 = 8 ∧ acceleratedOrbit 15 21137 = 4234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21137 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21137) = 3 ^ 8 * m + 4234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21137.1, data_15_21137.2]

/-- Complete interval computation for depth 15, residue 21138. -/
theorem bounds_15_21138 : exactInterval 15 21138 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21138 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21138) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21138 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21138 : oddCount 21138 15 = 8 ∧ acceleratedOrbit 15 21138 = 4234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21138 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21138) = 3 ^ 8 * m + 4234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21138.1, data_15_21138.2]

/-- Complete interval computation for depth 15, residue 21139. -/
theorem bounds_15_21139 : exactInterval 15 21139 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21139 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21139) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21139 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21139 : oddCount 21139 15 = 8 ∧ acceleratedOrbit 15 21139 = 4234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21139 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21139) = 3 ^ 8 * m + 4234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21139.1, data_15_21139.2]

/-- Complete interval computation for depth 15, residue 21140. -/
theorem bounds_15_21140 : exactInterval 15 21140 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21140 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21140) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21140 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21140 : oddCount 21140 15 = 8 ∧ acceleratedOrbit 15 21140 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21140 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21140) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21140.1, data_15_21140.2]

/-- Complete interval computation for depth 15, residue 21141. -/
theorem bounds_15_21141 : exactInterval 15 21141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21141 : oddCount 21141 15 = 8 ∧ acceleratedOrbit 15 21141 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21141) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21141.1, data_15_21141.2]

/-- Complete interval computation for depth 15, residue 21142. -/
theorem bounds_15_21142 : exactInterval 15 21142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21142 : oddCount 21142 15 = 8 ∧ acceleratedOrbit 15 21142 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21142) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21142.1, data_15_21142.2]

/-- Complete interval computation for depth 15, residue 21143. -/
theorem bounds_15_21143 : exactInterval 15 21143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21143 : oddCount 21143 15 = 8 ∧ acceleratedOrbit 15 21143 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21143) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21143.1, data_15_21143.2]

/-- Complete interval computation for depth 15, residue 21144. -/
theorem bounds_15_21144 : exactInterval 15 21144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21144 : oddCount 21144 15 = 8 ∧ acceleratedOrbit 15 21144 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21144) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21144.1, data_15_21144.2]

/-- Complete interval computation for depth 15, residue 21145. -/
theorem bounds_15_21145 : exactInterval 15 21145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21145 : oddCount 21145 15 = 7 ∧ acceleratedOrbit 15 21145 = 1412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21145) = 3 ^ 7 * m + 1412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21145.1, data_15_21145.2]

/-- Complete interval computation for depth 15, residue 21146. -/
theorem bounds_15_21146 : exactInterval 15 21146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21146 : oddCount 21146 15 = 8 ∧ acceleratedOrbit 15 21146 = 4238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21146) = 3 ^ 8 * m + 4238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21146.1, data_15_21146.2]

/-- Complete interval computation for depth 15, residue 21147. -/
theorem bounds_15_21147 : exactInterval 15 21147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21147 : oddCount 21147 15 = 12 ∧ acceleratedOrbit 15 21147 = 342994 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21147) = 3 ^ 12 * m + 342994 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21147.1, data_15_21147.2]

/-- Complete interval computation for depth 15, residue 21148. -/
theorem bounds_15_21148 : exactInterval 15 21148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21148 : oddCount 21148 15 = 9 ∧ acceleratedOrbit 15 21148 = 12707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21148) = 3 ^ 9 * m + 12707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21148.1, data_15_21148.2]

/-- Complete interval computation for depth 15, residue 21149. -/
theorem bounds_15_21149 : exactInterval 15 21149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21149 : oddCount 21149 15 = 9 ∧ acceleratedOrbit 15 21149 = 12707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21149) = 3 ^ 9 * m + 12707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21149.1, data_15_21149.2]

/-- Complete interval computation for depth 15, residue 21150. -/
theorem bounds_15_21150 : exactInterval 15 21150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21150 : oddCount 21150 15 = 9 ∧ acceleratedOrbit 15 21150 = 12707 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21150) = 3 ^ 9 * m + 12707 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21150.1, data_15_21150.2]

/-- Complete interval computation for depth 15, residue 21151. -/
theorem bounds_15_21151 : exactInterval 15 21151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21151 : oddCount 21151 15 = 10 ∧ acceleratedOrbit 15 21151 = 38117 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21151) = 3 ^ 10 * m + 38117 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21151.1, data_15_21151.2]

/-- Complete interval computation for depth 15, residue 21152. -/
theorem bounds_15_21152 : exactInterval 15 21152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21152 : oddCount 21152 15 = 5 ∧ acceleratedOrbit 15 21152 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21152) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21152.1, data_15_21152.2]

/-- Complete interval computation for depth 15, residue 21153. -/
theorem bounds_15_21153 : exactInterval 15 21153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21153 : oddCount 21153 15 = 7 ∧ acceleratedOrbit 15 21153 = 1412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21153) = 3 ^ 7 * m + 1412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21153.1, data_15_21153.2]

/-- Complete interval computation for depth 15, residue 21154. -/
theorem bounds_15_21154 : exactInterval 15 21154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21154 : oddCount 21154 15 = 9 ∧ acceleratedOrbit 15 21154 = 12712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21154) = 3 ^ 9 * m + 12712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21154.1, data_15_21154.2]

/-- Complete interval computation for depth 15, residue 21155. -/
theorem bounds_15_21155 : exactInterval 15 21155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21155 : oddCount 21155 15 = 9 ∧ acceleratedOrbit 15 21155 = 12712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21155) = 3 ^ 9 * m + 12712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21155.1, data_15_21155.2]

/-- Complete interval computation for depth 15, residue 21156. -/
theorem bounds_15_21156 : exactInterval 15 21156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21156 : oddCount 21156 15 = 9 ∧ acceleratedOrbit 15 21156 = 12712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21156) = 3 ^ 9 * m + 12712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21156.1, data_15_21156.2]

/-- Complete interval computation for depth 15, residue 21157. -/
theorem bounds_15_21157 : exactInterval 15 21157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21157 : oddCount 21157 15 = 9 ∧ acceleratedOrbit 15 21157 = 12712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21157) = 3 ^ 9 * m + 12712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21157.1, data_15_21157.2]

/-- Complete interval computation for depth 15, residue 21158. -/
theorem bounds_15_21158 : exactInterval 15 21158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21158 : oddCount 21158 15 = 9 ∧ acceleratedOrbit 15 21158 = 12712 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21158) = 3 ^ 9 * m + 12712 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21158.1, data_15_21158.2]

/-- Complete interval computation for depth 15, residue 21159. -/
theorem bounds_15_21159 : exactInterval 15 21159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21159 : oddCount 21159 15 = 11 ∧ acceleratedOrbit 15 21159 = 114398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21159) = 3 ^ 11 * m + 114398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21159.1, data_15_21159.2]

/-- Complete interval computation for depth 15, residue 21160. -/
theorem bounds_15_21160 : exactInterval 15 21160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21160 : oddCount 21160 15 = 5 ∧ acceleratedOrbit 15 21160 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21160) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21160.1, data_15_21160.2]

/-- Complete interval computation for depth 15, residue 21161. -/
theorem bounds_15_21161 : exactInterval 15 21161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21161 : oddCount 21161 15 = 12 ∧ acceleratedOrbit 15 21161 = 343223 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21161) = 3 ^ 12 * m + 343223 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21161.1, data_15_21161.2]

/-- Complete interval computation for depth 15, residue 21162. -/
theorem bounds_15_21162 : exactInterval 15 21162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21162 : oddCount 21162 15 = 5 ∧ acceleratedOrbit 15 21162 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21162) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21162.1, data_15_21162.2]

/-- Complete interval computation for depth 15, residue 21163. -/
theorem bounds_15_21163 : exactInterval 15 21163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21163 : oddCount 21163 15 = 9 ∧ acceleratedOrbit 15 21163 = 12716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21163) = 3 ^ 9 * m + 12716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21163.1, data_15_21163.2]

/-- Complete interval computation for depth 15, residue 21164. -/
theorem bounds_15_21164 : exactInterval 15 21164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21164 : oddCount 21164 15 = 5 ∧ acceleratedOrbit 15 21164 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21164) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21164.1, data_15_21164.2]

/-- Complete interval computation for depth 15, residue 21165. -/
theorem bounds_15_21165 : exactInterval 15 21165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21165 : oddCount 21165 15 = 5 ∧ acceleratedOrbit 15 21165 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21165) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21165.1, data_15_21165.2]

/-- Complete interval computation for depth 15, residue 21166. -/
theorem bounds_15_21166 : exactInterval 15 21166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21166 : oddCount 21166 15 = 5 ∧ acceleratedOrbit 15 21166 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21166) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21166.1, data_15_21166.2]

/-- Complete interval computation for depth 15, residue 21167. -/
theorem bounds_15_21167 : exactInterval 15 21167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21167 : oddCount 21167 15 = 10 ∧ acceleratedOrbit 15 21167 = 38150 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21167) = 3 ^ 10 * m + 38150 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21167.1, data_15_21167.2]

end Collatz.Research.PassageAtlas.Batch0646
