import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0407

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3164. -/
theorem bounds_12_3164 : exactInterval 12 3164 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3164 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3164) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3164 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3164 : oddCount 3164 12 = 6 ∧ acceleratedOrbit 12 3164 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3164 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3164) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3164.1, data_12_3164.2]

/-- Complete interval computation for depth 12, residue 3165. -/
theorem bounds_12_3165 : exactInterval 12 3165 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3165 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3165) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3165 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3165 : oddCount 3165 12 = 6 ∧ acceleratedOrbit 12 3165 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3165 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3165) = 3 ^ 6 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3165.1, data_12_3165.2]

/-- Complete interval computation for depth 12, residue 3166. -/
theorem bounds_12_3166 : exactInterval 12 3166 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3166 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3166) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3166 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3166 : oddCount 3166 12 = 9 ∧ acceleratedOrbit 12 3166 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3166 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3166) = 3 ^ 9 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3166.1, data_12_3166.2]

/-- Complete interval computation for depth 12, residue 3167. -/
theorem bounds_12_3167 : exactInterval 12 3167 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3167 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3167) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3167 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3167 : oddCount 3167 12 = 9 ∧ acceleratedOrbit 12 3167 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3167 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3167) = 3 ^ 9 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3167.1, data_12_3167.2]

/-- Complete interval computation for depth 12, residue 3168. -/
theorem bounds_12_3168 : exactInterval 12 3168 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3168 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3168) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3168 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3168 : oddCount 3168 12 = 2 ∧ acceleratedOrbit 12 3168 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3168 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3168) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3168.1, data_12_3168.2]

/-- Complete interval computation for depth 12, residue 3169. -/
theorem bounds_12_3169 : exactInterval 12 3169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3169 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3169) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3169 : oddCount 3169 12 = 7 ∧ acceleratedOrbit 12 3169 = 1694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3169 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3169) = 3 ^ 7 * m + 1694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3169.1, data_12_3169.2]

/-- Complete interval computation for depth 12, residue 3170. -/
theorem bounds_12_3170 : exactInterval 12 3170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3170 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3170) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3170 : oddCount 3170 12 = 7 ∧ acceleratedOrbit 12 3170 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3170 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3170) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3170.1, data_12_3170.2]

/-- Complete interval computation for depth 12, residue 3171. -/
theorem bounds_12_3171 : exactInterval 12 3171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3171 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3171) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3171 : oddCount 3171 12 = 7 ∧ acceleratedOrbit 12 3171 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3171 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3171) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3171.1, data_12_3171.2]

/-- Complete interval computation for depth 12, residue 3172. -/
theorem bounds_12_3172 : exactInterval 12 3172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3172 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3172) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3172 : oddCount 3172 12 = 7 ∧ acceleratedOrbit 12 3172 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3172 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3172) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3172.1, data_12_3172.2]

/-- Complete interval computation for depth 12, residue 3173. -/
theorem bounds_12_3173 : exactInterval 12 3173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3173 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3173) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3173 : oddCount 3173 12 = 7 ∧ acceleratedOrbit 12 3173 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3173 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3173) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3173.1, data_12_3173.2]

/-- Complete interval computation for depth 12, residue 3174. -/
theorem bounds_12_3174 : exactInterval 12 3174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3174 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3174) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3174 : oddCount 3174 12 = 7 ∧ acceleratedOrbit 12 3174 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3174 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3174) = 3 ^ 7 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3174.1, data_12_3174.2]

/-- Complete interval computation for depth 12, residue 3175. -/
theorem bounds_12_3175 : exactInterval 12 3175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3175 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3175) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3175 : oddCount 3175 12 = 10 ∧ acceleratedOrbit 12 3175 = 45791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3175 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3175) = 3 ^ 10 * m + 45791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3175.1, data_12_3175.2]

/-- Complete interval computation for depth 12, residue 3176. -/
theorem bounds_12_3176 : exactInterval 12 3176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3176 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3176) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3176 : oddCount 3176 12 = 2 ∧ acceleratedOrbit 12 3176 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3176 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3176) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3176.1, data_12_3176.2]

/-- Complete interval computation for depth 12, residue 3177. -/
theorem bounds_12_3177 : exactInterval 12 3177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3177 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3177) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3177 : oddCount 3177 12 = 8 ∧ acceleratedOrbit 12 3177 = 5093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3177 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3177) = 3 ^ 8 * m + 5093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3177.1, data_12_3177.2]

/-- Complete interval computation for depth 12, residue 3178. -/
theorem bounds_12_3178 : exactInterval 12 3178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3178 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3178) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3178 : oddCount 3178 12 = 2 ∧ acceleratedOrbit 12 3178 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3178 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3178) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3178.1, data_12_3178.2]

end Collatz.Research.StoppingAtlas.Batch0407
