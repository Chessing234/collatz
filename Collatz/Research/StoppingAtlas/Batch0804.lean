import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0804

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5166. -/
theorem bounds_13_5166 : exactInterval 13 5166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5166 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5166) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5166 : oddCount 5166 13 = 6 ∧ acceleratedOrbit 13 5166 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5166 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5166) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5166.1, data_13_5166.2]

/-- Complete interval computation for depth 13, residue 5167. -/
theorem bounds_13_5167 : exactInterval 13 5167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5167 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5167) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5167 : oddCount 5167 13 = 9 ∧ acceleratedOrbit 13 5167 = 12419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5167 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5167) = 3 ^ 9 * m + 12419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5167.1, data_13_5167.2]

/-- Complete interval computation for depth 13, residue 5168. -/
theorem bounds_13_5168 : exactInterval 13 5168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5168 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5168) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5168 : oddCount 5168 13 = 5 ∧ acceleratedOrbit 13 5168 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5168 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5168) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5168.1, data_13_5168.2]

/-- Complete interval computation for depth 13, residue 5169. -/
theorem bounds_13_5169 : exactInterval 13 5169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5169 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5169) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5169 : oddCount 5169 13 = 6 ∧ acceleratedOrbit 13 5169 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5169 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5169) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5169.1, data_13_5169.2]

/-- Complete interval computation for depth 13, residue 5170. -/
theorem bounds_13_5170 : exactInterval 13 5170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5170 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5170) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5170 : oddCount 5170 13 = 6 ∧ acceleratedOrbit 13 5170 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5170 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5170) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5170.1, data_13_5170.2]

/-- Complete interval computation for depth 13, residue 5171. -/
theorem bounds_13_5171 : exactInterval 13 5171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5171 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5171) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5171 : oddCount 5171 13 = 6 ∧ acceleratedOrbit 13 5171 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5171 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5171) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5171.1, data_13_5171.2]

/-- Complete interval computation for depth 13, residue 5172. -/
theorem bounds_13_5172 : exactInterval 13 5172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5172 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5172) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5172 : oddCount 5172 13 = 5 ∧ acceleratedOrbit 13 5172 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5172 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5172) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5172.1, data_13_5172.2]

/-- Complete interval computation for depth 13, residue 5173. -/
theorem bounds_13_5173 : exactInterval 13 5173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5173 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5173) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5173 : oddCount 5173 13 = 5 ∧ acceleratedOrbit 13 5173 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5173 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5173) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5173.1, data_13_5173.2]

/-- Complete interval computation for depth 13, residue 5174. -/
theorem bounds_13_5174 : exactInterval 13 5174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5174 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5174) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5174 : oddCount 5174 13 = 7 ∧ acceleratedOrbit 13 5174 = 1382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5174 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5174) = 3 ^ 7 * m + 1382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5174.1, data_13_5174.2]

/-- Complete interval computation for depth 13, residue 5175. -/
theorem bounds_13_5175 : exactInterval 13 5175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5175 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5175) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5175 : oddCount 5175 13 = 7 ∧ acceleratedOrbit 13 5175 = 1382 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5175 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5175) = 3 ^ 7 * m + 1382 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5175.1, data_13_5175.2]

/-- Complete interval computation for depth 13, residue 5176. -/
theorem bounds_13_5176 : exactInterval 13 5176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5176 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5176) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5176 : oddCount 5176 13 = 5 ∧ acceleratedOrbit 13 5176 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5176 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5176) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5176.1, data_13_5176.2]

/-- Complete interval computation for depth 13, residue 5177. -/
theorem bounds_13_5177 : exactInterval 13 5177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5177 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5177) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5177 : oddCount 5177 13 = 6 ∧ acceleratedOrbit 13 5177 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5177 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5177) = 3 ^ 6 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5177.1, data_13_5177.2]

/-- Complete interval computation for depth 13, residue 5178. -/
theorem bounds_13_5178 : exactInterval 13 5178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5178 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5178) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5178 : oddCount 5178 13 = 5 ∧ acceleratedOrbit 13 5178 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5178 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5178) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5178.1, data_13_5178.2]

/-- Complete interval computation for depth 13, residue 5179. -/
theorem bounds_13_5179 : exactInterval 13 5179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5179 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5179) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5179 : oddCount 5179 13 = 8 ∧ acceleratedOrbit 13 5179 = 4151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5179 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5179) = 3 ^ 8 * m + 4151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5179.1, data_13_5179.2]

/-- Complete interval computation for depth 13, residue 5180. -/
theorem bounds_13_5180 : exactInterval 13 5180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5180 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5180) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5180 : oddCount 5180 13 = 5 ∧ acceleratedOrbit 13 5180 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5180 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5180) = 3 ^ 5 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5180.1, data_13_5180.2]

end Collatz.Research.StoppingAtlas.Batch0804
