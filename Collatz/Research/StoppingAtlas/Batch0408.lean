import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0408

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3179. -/
theorem bounds_12_3179 : exactInterval 12 3179 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3179 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3179) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3179 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3179 : oddCount 3179 12 = 8 ∧ acceleratedOrbit 12 3179 = 5096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3179 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3179) = 3 ^ 8 * m + 5096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3179.1, data_12_3179.2]

/-- Complete interval computation for depth 12, residue 3180. -/
theorem bounds_12_3180 : exactInterval 12 3180 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3180 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3180) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3180 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3180 : oddCount 3180 12 = 9 ∧ acceleratedOrbit 12 3180 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3180 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3180) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3180.1, data_12_3180.2]

/-- Complete interval computation for depth 12, residue 3181. -/
theorem bounds_12_3181 : exactInterval 12 3181 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3181 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3181) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3181 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3181 : oddCount 3181 12 = 9 ∧ acceleratedOrbit 12 3181 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3181 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3181) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3181.1, data_12_3181.2]

/-- Complete interval computation for depth 12, residue 3182. -/
theorem bounds_12_3182 : exactInterval 12 3182 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3182 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3182) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3182 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3182 : oddCount 3182 12 = 9 ∧ acceleratedOrbit 12 3182 = 15308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3182 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3182) = 3 ^ 9 * m + 15308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3182.1, data_12_3182.2]

/-- Complete interval computation for depth 12, residue 3183. -/
theorem bounds_12_3183 : exactInterval 12 3183 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3183 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3183) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3183 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3183 : oddCount 3183 12 = 9 ∧ acceleratedOrbit 12 3183 = 15302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3183 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3183) = 3 ^ 9 * m + 15302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3183.1, data_12_3183.2]

/-- Complete interval computation for depth 12, residue 3184. -/
theorem bounds_12_3184 : exactInterval 12 3184 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3184 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3184) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3184 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3184 : oddCount 3184 12 = 5 ∧ acceleratedOrbit 12 3184 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3184 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3184) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3184.1, data_12_3184.2]

/-- Complete interval computation for depth 12, residue 3185. -/
theorem bounds_12_3185 : exactInterval 12 3185 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3185 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3185) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3185 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3185 : oddCount 3185 12 = 2 ∧ acceleratedOrbit 12 3185 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3185 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3185) = 3 ^ 2 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3185.1, data_12_3185.2]

/-- Complete interval computation for depth 12, residue 3186. -/
theorem bounds_12_3186 : exactInterval 12 3186 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3186 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3186) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3186 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3186 : oddCount 3186 12 = 6 ∧ acceleratedOrbit 12 3186 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3186 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3186) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3186.1, data_12_3186.2]

/-- Complete interval computation for depth 12, residue 3187. -/
theorem bounds_12_3187 : exactInterval 12 3187 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3187 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3187) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3187 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3187 : oddCount 3187 12 = 6 ∧ acceleratedOrbit 12 3187 = 568 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3187 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3187) = 3 ^ 6 * m + 568 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3187.1, data_12_3187.2]

/-- Complete interval computation for depth 12, residue 3188. -/
theorem bounds_12_3188 : exactInterval 12 3188 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3188 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3188) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3188 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3188 : oddCount 3188 12 = 5 ∧ acceleratedOrbit 12 3188 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3188 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3188) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3188.1, data_12_3188.2]

/-- Complete interval computation for depth 12, residue 3189. -/
theorem bounds_12_3189 : exactInterval 12 3189 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3189 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3189) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3189 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3189 : oddCount 3189 12 = 5 ∧ acceleratedOrbit 12 3189 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3189 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3189) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3189.1, data_12_3189.2]

/-- Complete interval computation for depth 12, residue 3190. -/
theorem bounds_12_3190 : exactInterval 12 3190 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3190 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3190) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3190 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3190 : oddCount 3190 12 = 6 ∧ acceleratedOrbit 12 3190 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3190 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3190) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3190.1, data_12_3190.2]

/-- Complete interval computation for depth 12, residue 3191. -/
theorem bounds_12_3191 : exactInterval 12 3191 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3191 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3191) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3191 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3191 : oddCount 3191 12 = 6 ∧ acceleratedOrbit 12 3191 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3191 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3191) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3191.1, data_12_3191.2]

/-- Complete interval computation for depth 12, residue 3192. -/
theorem bounds_12_3192 : exactInterval 12 3192 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3192 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3192) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3192 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3192 : oddCount 3192 12 = 5 ∧ acceleratedOrbit 12 3192 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3192 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3192) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3192.1, data_12_3192.2]

/-- Complete interval computation for depth 12, residue 3193. -/
theorem bounds_12_3193 : exactInterval 12 3193 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3193 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3193) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3193 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3193 : oddCount 3193 12 = 7 ∧ acceleratedOrbit 12 3193 = 1706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3193 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3193) = 3 ^ 7 * m + 1706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3193.1, data_12_3193.2]

end Collatz.Research.StoppingAtlas.Batch0408
