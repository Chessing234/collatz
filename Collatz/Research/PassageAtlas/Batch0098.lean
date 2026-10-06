import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0098

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3178. -/
theorem bounds_15_3178 : exactInterval 15 3178 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3178 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3178) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3178 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3178 : oddCount 3178 15 = 5 ∧ acceleratedOrbit 15 3178 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3178 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3178) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3178.1, data_15_3178.2]

/-- Complete interval computation for depth 15, residue 3179. -/
theorem bounds_15_3179 : exactInterval 15 3179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3179 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3179) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3179 : oddCount 3179 15 = 8 ∧ acceleratedOrbit 15 3179 = 637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3179 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3179) = 3 ^ 8 * m + 637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3179.1, data_15_3179.2]

/-- Complete interval computation for depth 15, residue 3180. -/
theorem bounds_15_3180 : exactInterval 15 3180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3180 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3180) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3180 : oddCount 3180 15 = 10 ∧ acceleratedOrbit 15 3180 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3180 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3180) = 3 ^ 10 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3180.1, data_15_3180.2]

/-- Complete interval computation for depth 15, residue 3181. -/
theorem bounds_15_3181 : exactInterval 15 3181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3181 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3181) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3181 : oddCount 3181 15 = 10 ∧ acceleratedOrbit 15 3181 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3181 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3181) = 3 ^ 10 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3181.1, data_15_3181.2]

/-- Complete interval computation for depth 15, residue 3182. -/
theorem bounds_15_3182 : exactInterval 15 3182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3182 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3182) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3182 : oddCount 3182 15 = 10 ∧ acceleratedOrbit 15 3182 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3182 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3182) = 3 ^ 10 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3182.1, data_15_3182.2]

/-- Complete interval computation for depth 15, residue 3183. -/
theorem bounds_15_3183 : exactInterval 15 3183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3183 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3183) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3183 : oddCount 3183 15 = 11 ∧ acceleratedOrbit 15 3183 = 17216 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3183 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3183) = 3 ^ 11 * m + 17216 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3183.1, data_15_3183.2]

/-- Complete interval computation for depth 15, residue 3184. -/
theorem bounds_15_3184 : exactInterval 15 3184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3184 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3184) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3184 : oddCount 3184 15 = 7 ∧ acceleratedOrbit 15 3184 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3184 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3184) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3184.1, data_15_3184.2]

/-- Complete interval computation for depth 15, residue 3185. -/
theorem bounds_15_3185 : exactInterval 15 3185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3185 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3185) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3185 : oddCount 3185 15 = 5 ∧ acceleratedOrbit 15 3185 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3185 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3185) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3185.1, data_15_3185.2]

/-- Complete interval computation for depth 15, residue 3186. -/
theorem bounds_15_3186 : exactInterval 15 3186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3186 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3186) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3186 : oddCount 3186 15 = 6 ∧ acceleratedOrbit 15 3186 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3186 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3186) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3186.1, data_15_3186.2]

/-- Complete interval computation for depth 15, residue 3187. -/
theorem bounds_15_3187 : exactInterval 15 3187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3187 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3187) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3187 : oddCount 3187 15 = 6 ∧ acceleratedOrbit 15 3187 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3187 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3187) = 3 ^ 6 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3187.1, data_15_3187.2]

/-- Complete interval computation for depth 15, residue 3188. -/
theorem bounds_15_3188 : exactInterval 15 3188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3188 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3188) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3188 : oddCount 3188 15 = 7 ∧ acceleratedOrbit 15 3188 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3188 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3188) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3188.1, data_15_3188.2]

/-- Complete interval computation for depth 15, residue 3189. -/
theorem bounds_15_3189 : exactInterval 15 3189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3189 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3189) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3189 : oddCount 3189 15 = 7 ∧ acceleratedOrbit 15 3189 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3189 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3189) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3189.1, data_15_3189.2]

/-- Complete interval computation for depth 15, residue 3190. -/
theorem bounds_15_3190 : exactInterval 15 3190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3190 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3190) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3190 : oddCount 3190 15 = 8 ∧ acceleratedOrbit 15 3190 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3190 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3190) = 3 ^ 8 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3190.1, data_15_3190.2]

/-- Complete interval computation for depth 15, residue 3191. -/
theorem bounds_15_3191 : exactInterval 15 3191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3191 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3191) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3191 : oddCount 3191 15 = 8 ∧ acceleratedOrbit 15 3191 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3191 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3191) = 3 ^ 8 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3191.1, data_15_3191.2]

/-- Complete interval computation for depth 15, residue 3192. -/
theorem bounds_15_3192 : exactInterval 15 3192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3192 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3192) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3192 : oddCount 3192 15 = 7 ∧ acceleratedOrbit 15 3192 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3192 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3192) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3192.1, data_15_3192.2]

/-- Complete interval computation for depth 15, residue 3193. -/
theorem bounds_15_3193 : exactInterval 15 3193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3193 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3193) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3193 : oddCount 3193 15 = 8 ∧ acceleratedOrbit 15 3193 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3193 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3193) = 3 ^ 8 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3193.1, data_15_3193.2]

/-- Complete interval computation for depth 15, residue 3194. -/
theorem bounds_15_3194 : exactInterval 15 3194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3194 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3194) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3194 : oddCount 3194 15 = 7 ∧ acceleratedOrbit 15 3194 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3194 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3194) = 3 ^ 7 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3194.1, data_15_3194.2]

/-- Complete interval computation for depth 15, residue 3195. -/
theorem bounds_15_3195 : exactInterval 15 3195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3195 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3195) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3195 : oddCount 3195 15 = 8 ∧ acceleratedOrbit 15 3195 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3195 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3195) = 3 ^ 8 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3195.1, data_15_3195.2]

/-- Complete interval computation for depth 15, residue 3196. -/
theorem bounds_15_3196 : exactInterval 15 3196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3196 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3196) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3196 : oddCount 3196 15 = 8 ∧ acceleratedOrbit 15 3196 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3196 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3196) = 3 ^ 8 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3196.1, data_15_3196.2]

/-- Complete interval computation for depth 15, residue 3197. -/
theorem bounds_15_3197 : exactInterval 15 3197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3197 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3197) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3197 : oddCount 3197 15 = 8 ∧ acceleratedOrbit 15 3197 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3197 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3197) = 3 ^ 8 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3197.1, data_15_3197.2]

/-- Complete interval computation for depth 15, residue 3198. -/
theorem bounds_15_3198 : exactInterval 15 3198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3198 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3198) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3198 : oddCount 3198 15 = 8 ∧ acceleratedOrbit 15 3198 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3198 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3198) = 3 ^ 8 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3198.1, data_15_3198.2]

/-- Complete interval computation for depth 15, residue 3199. -/
theorem bounds_15_3199 : exactInterval 15 3199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3199 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3199) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3199 : oddCount 3199 15 = 11 ∧ acceleratedOrbit 15 3199 = 17300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3199 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3199) = 3 ^ 11 * m + 17300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3199.1, data_15_3199.2]

/-- Complete interval computation for depth 15, residue 3200. -/
theorem bounds_15_3200 : exactInterval 15 3200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3200 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3200) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3200 : oddCount 3200 15 = 5 ∧ acceleratedOrbit 15 3200 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3200 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3200) = 3 ^ 5 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3200.1, data_15_3200.2]

/-- Complete interval computation for depth 15, residue 3201. -/
theorem bounds_15_3201 : exactInterval 15 3201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3201 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3201) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3201 : oddCount 3201 15 = 10 ∧ acceleratedOrbit 15 3201 = 5777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3201 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3201) = 3 ^ 10 * m + 5777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3201.1, data_15_3201.2]

/-- Complete interval computation for depth 15, residue 3202. -/
theorem bounds_15_3202 : exactInterval 15 3202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3202 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3202) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3202 : oddCount 3202 15 = 8 ∧ acceleratedOrbit 15 3202 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3202 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3202) = 3 ^ 8 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3202.1, data_15_3202.2]

/-- Complete interval computation for depth 15, residue 3203. -/
theorem bounds_15_3203 : exactInterval 15 3203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3203 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3203) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3203 : oddCount 3203 15 = 8 ∧ acceleratedOrbit 15 3203 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3203 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3203) = 3 ^ 8 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3203.1, data_15_3203.2]

/-- Complete interval computation for depth 15, residue 3204. -/
theorem bounds_15_3204 : exactInterval 15 3204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3204 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3204) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3204 : oddCount 3204 15 = 8 ∧ acceleratedOrbit 15 3204 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3204 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3204) = 3 ^ 8 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3204.1, data_15_3204.2]

/-- Complete interval computation for depth 15, residue 3205. -/
theorem bounds_15_3205 : exactInterval 15 3205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3205 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3205) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3205 : oddCount 3205 15 = 8 ∧ acceleratedOrbit 15 3205 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3205 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3205) = 3 ^ 8 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3205.1, data_15_3205.2]

/-- Complete interval computation for depth 15, residue 3206. -/
theorem bounds_15_3206 : exactInterval 15 3206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3206 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3206) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3206 : oddCount 3206 15 = 8 ∧ acceleratedOrbit 15 3206 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3206 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3206) = 3 ^ 8 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3206.1, data_15_3206.2]

/-- Complete interval computation for depth 15, residue 3207. -/
theorem bounds_15_3207 : exactInterval 15 3207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3207 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3207) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3207 : oddCount 3207 15 = 8 ∧ acceleratedOrbit 15 3207 = 643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3207 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3207) = 3 ^ 8 * m + 643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3207.1, data_15_3207.2]

/-- Complete interval computation for depth 15, residue 3208. -/
theorem bounds_15_3208 : exactInterval 15 3208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3208 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3208) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3208 : oddCount 3208 15 = 4 ∧ acceleratedOrbit 15 3208 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3208 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3208) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3208.1, data_15_3208.2]

/-- Complete interval computation for depth 15, residue 3209. -/
theorem bounds_15_3209 : exactInterval 15 3209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3209 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3209) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3209 : oddCount 3209 15 = 11 ∧ acceleratedOrbit 15 3209 = 17360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3209 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3209) = 3 ^ 11 * m + 17360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3209.1, data_15_3209.2]

/-- Complete interval computation for depth 15, residue 3210. -/
theorem bounds_15_3210 : exactInterval 15 3210 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3210 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3210) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3210 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3210 : oddCount 3210 15 = 4 ∧ acceleratedOrbit 15 3210 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3210 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3210) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3210.1, data_15_3210.2]

end Collatz.Research.PassageAtlas.Batch0098
