import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0675

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3184. -/
theorem bounds_13_3184 : exactInterval 13 3184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3184 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3184) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3184 : oddCount 3184 13 = 5 ∧ acceleratedOrbit 13 3184 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3184 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3184) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3184.1, data_13_3184.2]

/-- Complete interval computation for depth 13, residue 3185. -/
theorem bounds_13_3185 : exactInterval 13 3185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3185 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3185) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3185 : oddCount 3185 13 = 3 ∧ acceleratedOrbit 13 3185 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3185 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3185) = 3 ^ 3 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3185.1, data_13_3185.2]

/-- Complete interval computation for depth 13, residue 3186. -/
theorem bounds_13_3186 : exactInterval 13 3186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3186 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3186) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3186 : oddCount 3186 13 = 6 ∧ acceleratedOrbit 13 3186 = 284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3186 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3186) = 3 ^ 6 * m + 284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3186.1, data_13_3186.2]

/-- Complete interval computation for depth 13, residue 3187. -/
theorem bounds_13_3187 : exactInterval 13 3187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3187 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3187) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3187 : oddCount 3187 13 = 6 ∧ acceleratedOrbit 13 3187 = 284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3187 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3187) = 3 ^ 6 * m + 284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3187.1, data_13_3187.2]

/-- Complete interval computation for depth 13, residue 3188. -/
theorem bounds_13_3188 : exactInterval 13 3188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3188 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3188) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3188 : oddCount 3188 13 = 5 ∧ acceleratedOrbit 13 3188 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3188 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3188) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3188.1, data_13_3188.2]

/-- Complete interval computation for depth 13, residue 3189. -/
theorem bounds_13_3189 : exactInterval 13 3189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3189 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3189) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3189 : oddCount 3189 13 = 5 ∧ acceleratedOrbit 13 3189 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3189 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3189) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3189.1, data_13_3189.2]

/-- Complete interval computation for depth 13, residue 3190. -/
theorem bounds_13_3190 : exactInterval 13 3190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3190 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3190) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3190 : oddCount 3190 13 = 7 ∧ acceleratedOrbit 13 3190 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3190 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3190) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3190.1, data_13_3190.2]

/-- Complete interval computation for depth 13, residue 3191. -/
theorem bounds_13_3191 : exactInterval 13 3191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3191 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3191) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3191 : oddCount 3191 13 = 7 ∧ acceleratedOrbit 13 3191 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3191 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3191) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3191.1, data_13_3191.2]

/-- Complete interval computation for depth 13, residue 3192. -/
theorem bounds_13_3192 : exactInterval 13 3192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3192 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3192) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3192 : oddCount 3192 13 = 5 ∧ acceleratedOrbit 13 3192 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3192 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3192) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3192.1, data_13_3192.2]

/-- Complete interval computation for depth 13, residue 3193. -/
theorem bounds_13_3193 : exactInterval 13 3193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3193 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3193) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3193 : oddCount 3193 13 = 7 ∧ acceleratedOrbit 13 3193 = 853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3193 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3193) = 3 ^ 7 * m + 853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3193.1, data_13_3193.2]

/-- Complete interval computation for depth 13, residue 3194. -/
theorem bounds_13_3194 : exactInterval 13 3194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3194 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3194) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3194 : oddCount 3194 13 = 5 ∧ acceleratedOrbit 13 3194 = 95 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3194 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3194) = 3 ^ 5 * m + 95 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3194.1, data_13_3194.2]

/-- Complete interval computation for depth 13, residue 3195. -/
theorem bounds_13_3195 : exactInterval 13 3195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3195 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3195) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3195 : oddCount 3195 13 = 7 ∧ acceleratedOrbit 13 3195 = 854 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3195 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3195) = 3 ^ 7 * m + 854 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3195.1, data_13_3195.2]

/-- Complete interval computation for depth 13, residue 3196. -/
theorem bounds_13_3196 : exactInterval 13 3196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3196 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3196) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3196 : oddCount 3196 13 = 8 ∧ acceleratedOrbit 13 3196 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3196 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3196) = 3 ^ 8 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3196.1, data_13_3196.2]

/-- Complete interval computation for depth 13, residue 3197. -/
theorem bounds_13_3197 : exactInterval 13 3197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3197 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3197) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3197 : oddCount 3197 13 = 8 ∧ acceleratedOrbit 13 3197 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3197 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3197) = 3 ^ 8 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3197.1, data_13_3197.2]

/-- Complete interval computation for depth 13, residue 3198. -/
theorem bounds_13_3198 : exactInterval 13 3198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3198 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3198) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3198 : oddCount 3198 13 = 8 ∧ acceleratedOrbit 13 3198 = 2564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3198 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3198) = 3 ^ 8 * m + 2564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3198.1, data_13_3198.2]

/-- Complete interval computation for depth 13, residue 3199. -/
theorem bounds_13_3199 : exactInterval 13 3199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3199 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3199) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3199 : oddCount 3199 13 = 11 ∧ acceleratedOrbit 13 3199 = 69200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3199 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3199) = 3 ^ 11 * m + 69200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3199.1, data_13_3199.2]

end Collatz.Research.StoppingAtlas.Batch0675
