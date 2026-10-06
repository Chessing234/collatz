import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0674

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3169. -/
theorem bounds_13_3169 : exactInterval 13 3169 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3169 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3169) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3169 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3169 : oddCount 3169 13 = 7 ∧ acceleratedOrbit 13 3169 = 847 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3169 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3169) = 3 ^ 7 * m + 847 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3169.1, data_13_3169.2]

/-- Complete interval computation for depth 13, residue 3170. -/
theorem bounds_13_3170 : exactInterval 13 3170 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3170 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3170) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3170 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3170 : oddCount 3170 13 = 7 ∧ acceleratedOrbit 13 3170 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3170 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3170) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3170.1, data_13_3170.2]

/-- Complete interval computation for depth 13, residue 3171. -/
theorem bounds_13_3171 : exactInterval 13 3171 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3171 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3171) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3171 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3171 : oddCount 3171 13 = 7 ∧ acceleratedOrbit 13 3171 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3171 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3171) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3171.1, data_13_3171.2]

/-- Complete interval computation for depth 13, residue 3172. -/
theorem bounds_13_3172 : exactInterval 13 3172 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3172 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3172) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3172 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3172 : oddCount 3172 13 = 7 ∧ acceleratedOrbit 13 3172 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3172 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3172) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3172.1, data_13_3172.2]

/-- Complete interval computation for depth 13, residue 3173. -/
theorem bounds_13_3173 : exactInterval 13 3173 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3173 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3173) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3173 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3173 : oddCount 3173 13 = 7 ∧ acceleratedOrbit 13 3173 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3173 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3173) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3173.1, data_13_3173.2]

/-- Complete interval computation for depth 13, residue 3174. -/
theorem bounds_13_3174 : exactInterval 13 3174 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3174 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3174) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3174 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3174 : oddCount 3174 13 = 7 ∧ acceleratedOrbit 13 3174 = 850 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3174 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3174) = 3 ^ 7 * m + 850 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3174.1, data_13_3174.2]

/-- Complete interval computation for depth 13, residue 3175. -/
theorem bounds_13_3175 : exactInterval 13 3175 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3175 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3175) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3175 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3175 : oddCount 3175 13 = 11 ∧ acceleratedOrbit 13 3175 = 68687 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3175 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3175) = 3 ^ 11 * m + 68687 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3175.1, data_13_3175.2]

/-- Complete interval computation for depth 13, residue 3176. -/
theorem bounds_13_3176 : exactInterval 13 3176 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3176 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3176) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3176 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3176 : oddCount 3176 13 = 3 ∧ acceleratedOrbit 13 3176 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3176 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3176) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3176.1, data_13_3176.2]

/-- Complete interval computation for depth 13, residue 3177. -/
theorem bounds_13_3177 : exactInterval 13 3177 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3177 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3177) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3177 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3177 : oddCount 3177 13 = 9 ∧ acceleratedOrbit 13 3177 = 7640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3177 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3177) = 3 ^ 9 * m + 7640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3177.1, data_13_3177.2]

/-- Complete interval computation for depth 13, residue 3178. -/
theorem bounds_13_3178 : exactInterval 13 3178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3178 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3178) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3178 : oddCount 3178 13 = 3 ∧ acceleratedOrbit 13 3178 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3178 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3178) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3178.1, data_13_3178.2]

/-- Complete interval computation for depth 13, residue 3179. -/
theorem bounds_13_3179 : exactInterval 13 3179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3179 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3179) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3179 : oddCount 3179 13 = 8 ∧ acceleratedOrbit 13 3179 = 2548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3179 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3179) = 3 ^ 8 * m + 2548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3179.1, data_13_3179.2]

/-- Complete interval computation for depth 13, residue 3180. -/
theorem bounds_13_3180 : exactInterval 13 3180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3180 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3180) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3180 : oddCount 3180 13 = 9 ∧ acceleratedOrbit 13 3180 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3180 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3180) = 3 ^ 9 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3180.1, data_13_3180.2]

/-- Complete interval computation for depth 13, residue 3181. -/
theorem bounds_13_3181 : exactInterval 13 3181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3181 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3181) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3181 : oddCount 3181 13 = 9 ∧ acceleratedOrbit 13 3181 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3181 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3181) = 3 ^ 9 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3181.1, data_13_3181.2]

/-- Complete interval computation for depth 13, residue 3182. -/
theorem bounds_13_3182 : exactInterval 13 3182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3182 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3182) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3182 : oddCount 3182 13 = 9 ∧ acceleratedOrbit 13 3182 = 7654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3182 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3182) = 3 ^ 9 * m + 7654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3182.1, data_13_3182.2]

/-- Complete interval computation for depth 13, residue 3183. -/
theorem bounds_13_3183 : exactInterval 13 3183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3183 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3183) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3183 : oddCount 3183 13 = 9 ∧ acceleratedOrbit 13 3183 = 7651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3183 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3183) = 3 ^ 9 * m + 7651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3183.1, data_13_3183.2]

end Collatz.Research.StoppingAtlas.Batch0674
