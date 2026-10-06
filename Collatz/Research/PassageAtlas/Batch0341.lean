import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0341

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11141. -/
theorem bounds_15_11141 : exactInterval 15 11141 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11141 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11141) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11141 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11141 : oddCount 11141 15 = 9 ∧ acceleratedOrbit 15 11141 = 6698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11141 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11141) = 3 ^ 9 * m + 6698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11141.1, data_15_11141.2]

/-- Complete interval computation for depth 15, residue 11142. -/
theorem bounds_15_11142 : exactInterval 15 11142 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11142 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11142) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11142 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11142 : oddCount 11142 15 = 9 ∧ acceleratedOrbit 15 11142 = 6698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11142 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11142) = 3 ^ 9 * m + 6698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11142.1, data_15_11142.2]

/-- Complete interval computation for depth 15, residue 11143. -/
theorem bounds_15_11143 : exactInterval 15 11143 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11143 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11143) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11143 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11143 : oddCount 11143 15 = 6 ∧ acceleratedOrbit 15 11143 = 248 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11143 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11143) = 3 ^ 6 * m + 248 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11143.1, data_15_11143.2]

/-- Complete interval computation for depth 15, residue 11144. -/
theorem bounds_15_11144 : exactInterval 15 11144 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11144 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11144) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11144 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11144 : oddCount 11144 15 = 4 ∧ acceleratedOrbit 15 11144 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11144 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11144) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11144.1, data_15_11144.2]

/-- Complete interval computation for depth 15, residue 11145. -/
theorem bounds_15_11145 : exactInterval 15 11145 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11145 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11145) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11145 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11145 : oddCount 11145 15 = 12 ∧ acceleratedOrbit 15 11145 = 180791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11145 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11145) = 3 ^ 12 * m + 180791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11145.1, data_15_11145.2]

/-- Complete interval computation for depth 15, residue 11146. -/
theorem bounds_15_11146 : exactInterval 15 11146 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11146 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11146) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11146 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11146 : oddCount 11146 15 = 4 ∧ acceleratedOrbit 15 11146 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11146 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11146) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11146.1, data_15_11146.2]

/-- Complete interval computation for depth 15, residue 11147. -/
theorem bounds_15_11147 : exactInterval 15 11147 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11147 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11147) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11147 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11147 : oddCount 11147 15 = 9 ∧ acceleratedOrbit 15 11147 = 6698 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11147 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11147) = 3 ^ 9 * m + 6698 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11147.1, data_15_11147.2]

/-- Complete interval computation for depth 15, residue 11148. -/
theorem bounds_15_11148 : exactInterval 15 11148 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11148 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11148) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11148 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11148 : oddCount 11148 15 = 4 ∧ acceleratedOrbit 15 11148 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11148 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11148) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11148.1, data_15_11148.2]

/-- Complete interval computation for depth 15, residue 11149. -/
theorem bounds_15_11149 : exactInterval 15 11149 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11149 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11149) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11149 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11149 : oddCount 11149 15 = 4 ∧ acceleratedOrbit 15 11149 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11149 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11149) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11149.1, data_15_11149.2]

/-- Complete interval computation for depth 15, residue 11150. -/
theorem bounds_15_11150 : exactInterval 15 11150 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11150 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11150) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11150 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11150 : oddCount 11150 15 = 8 ∧ acceleratedOrbit 15 11150 = 2234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11150 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11150) = 3 ^ 8 * m + 2234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11150.1, data_15_11150.2]

/-- Complete interval computation for depth 15, residue 11151. -/
theorem bounds_15_11151 : exactInterval 15 11151 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11151 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11151) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11151 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11151 : oddCount 11151 15 = 8 ∧ acceleratedOrbit 15 11151 = 2234 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11151 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11151) = 3 ^ 8 * m + 2234 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11151.1, data_15_11151.2]

/-- Complete interval computation for depth 15, residue 11152. -/
theorem bounds_15_11152 : exactInterval 15 11152 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11152 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11152) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11152 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11152 : oddCount 11152 15 = 5 ∧ acceleratedOrbit 15 11152 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11152 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11152) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11152.1, data_15_11152.2]

/-- Complete interval computation for depth 15, residue 11153. -/
theorem bounds_15_11153 : exactInterval 15 11153 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11153 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11153) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11153 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11153 : oddCount 11153 15 = 7 ∧ acceleratedOrbit 15 11153 = 746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11153 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11153) = 3 ^ 7 * m + 746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11153.1, data_15_11153.2]

/-- Complete interval computation for depth 15, residue 11154. -/
theorem bounds_15_11154 : exactInterval 15 11154 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11154 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11154) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11154 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11154 : oddCount 11154 15 = 7 ∧ acceleratedOrbit 15 11154 = 746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11154 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11154) = 3 ^ 7 * m + 746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11154.1, data_15_11154.2]

/-- Complete interval computation for depth 15, residue 11155. -/
theorem bounds_15_11155 : exactInterval 15 11155 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11155 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11155) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11155 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11155 : oddCount 11155 15 = 7 ∧ acceleratedOrbit 15 11155 = 746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11155 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11155) = 3 ^ 7 * m + 746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11155.1, data_15_11155.2]

/-- Complete interval computation for depth 15, residue 11156. -/
theorem bounds_15_11156 : exactInterval 15 11156 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11156 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11156) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11156 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11156 : oddCount 11156 15 = 5 ∧ acceleratedOrbit 15 11156 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11156 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11156) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11156.1, data_15_11156.2]

/-- Complete interval computation for depth 15, residue 11157. -/
theorem bounds_15_11157 : exactInterval 15 11157 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11157 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11157) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11157 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11157 : oddCount 11157 15 = 5 ∧ acceleratedOrbit 15 11157 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11157 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11157) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11157.1, data_15_11157.2]

/-- Complete interval computation for depth 15, residue 11158. -/
theorem bounds_15_11158 : exactInterval 15 11158 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11158 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11158) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11158 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11158 : oddCount 11158 15 = 7 ∧ acceleratedOrbit 15 11158 = 746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11158 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11158) = 3 ^ 7 * m + 746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11158.1, data_15_11158.2]

/-- Complete interval computation for depth 15, residue 11159. -/
theorem bounds_15_11159 : exactInterval 15 11159 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11159 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11159) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11159 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11159 : oddCount 11159 15 = 7 ∧ acceleratedOrbit 15 11159 = 746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11159 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11159) = 3 ^ 7 * m + 746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11159.1, data_15_11159.2]

/-- Complete interval computation for depth 15, residue 11160. -/
theorem bounds_15_11160 : exactInterval 15 11160 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11160 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11160) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11160 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11160 : oddCount 11160 15 = 5 ∧ acceleratedOrbit 15 11160 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11160 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11160) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11160.1, data_15_11160.2]

/-- Complete interval computation for depth 15, residue 11161. -/
theorem bounds_15_11161 : exactInterval 15 11161 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11161 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11161) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11161 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11161 : oddCount 11161 15 = 7 ∧ acceleratedOrbit 15 11161 = 746 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11161 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11161) = 3 ^ 7 * m + 746 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11161.1, data_15_11161.2]

/-- Complete interval computation for depth 15, residue 11162. -/
theorem bounds_15_11162 : exactInterval 15 11162 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11162 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11162) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11162 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11162 : oddCount 11162 15 = 5 ∧ acceleratedOrbit 15 11162 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11162 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11162) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11162.1, data_15_11162.2]

/-- Complete interval computation for depth 15, residue 11163. -/
theorem bounds_15_11163 : exactInterval 15 11163 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11163 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11163) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11163 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11163 : oddCount 11163 15 = 8 ∧ acceleratedOrbit 15 11163 = 2236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11163 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11163) = 3 ^ 8 * m + 2236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11163.1, data_15_11163.2]

/-- Complete interval computation for depth 15, residue 11164. -/
theorem bounds_15_11164 : exactInterval 15 11164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11164 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11164) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11164 : oddCount 11164 15 = 10 ∧ acceleratedOrbit 15 11164 = 20128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11164 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11164) = 3 ^ 10 * m + 20128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11164.1, data_15_11164.2]

/-- Complete interval computation for depth 15, residue 11165. -/
theorem bounds_15_11165 : exactInterval 15 11165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11165 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11165) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11165 : oddCount 11165 15 = 10 ∧ acceleratedOrbit 15 11165 = 20128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11165 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11165) = 3 ^ 10 * m + 20128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11165.1, data_15_11165.2]

/-- Complete interval computation for depth 15, residue 11166. -/
theorem bounds_15_11166 : exactInterval 15 11166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11166 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11166) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11166 : oddCount 11166 15 = 10 ∧ acceleratedOrbit 15 11166 = 20128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11166 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11166) = 3 ^ 10 * m + 20128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11166.1, data_15_11166.2]

/-- Complete interval computation for depth 15, residue 11167. -/
theorem bounds_15_11167 : exactInterval 15 11167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11167 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11167) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11167 : oddCount 11167 15 = 9 ∧ acceleratedOrbit 15 11167 = 6709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11167 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11167) = 3 ^ 9 * m + 6709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11167.1, data_15_11167.2]

/-- Complete interval computation for depth 15, residue 11168. -/
theorem bounds_15_11168 : exactInterval 15 11168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11168 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11168) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11168 : oddCount 11168 15 = 4 ∧ acceleratedOrbit 15 11168 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11168 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11168) = 3 ^ 4 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11168.1, data_15_11168.2]

/-- Complete interval computation for depth 15, residue 11169. -/
theorem bounds_15_11169 : exactInterval 15 11169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11169 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11169) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11169 : oddCount 11169 15 = 9 ∧ acceleratedOrbit 15 11169 = 6713 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11169 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11169) = 3 ^ 9 * m + 6713 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11169.1, data_15_11169.2]

/-- Complete interval computation for depth 15, residue 11170. -/
theorem bounds_15_11170 : exactInterval 15 11170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11170 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11170) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11170 : oddCount 11170 15 = 5 ∧ acceleratedOrbit 15 11170 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11170 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11170) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11170.1, data_15_11170.2]

/-- Complete interval computation for depth 15, residue 11171. -/
theorem bounds_15_11171 : exactInterval 15 11171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11171 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11171) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11171 : oddCount 11171 15 = 5 ∧ acceleratedOrbit 15 11171 = 83 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11171 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11171) = 3 ^ 5 * m + 83 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11171.1, data_15_11171.2]

/-- Complete interval computation for depth 15, residue 11172. -/
theorem bounds_15_11172 : exactInterval 15 11172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11172 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11172) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11172 : oddCount 11172 15 = 9 ∧ acceleratedOrbit 15 11172 = 6716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11172 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11172) = 3 ^ 9 * m + 6716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11172.1, data_15_11172.2]

end Collatz.Research.PassageAtlas.Batch0341
