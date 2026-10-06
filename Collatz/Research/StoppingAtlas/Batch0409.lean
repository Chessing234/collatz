import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0409

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3194. -/
theorem bounds_12_3194 : exactInterval 12 3194 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3194 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3194) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3194 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3194 : oddCount 3194 12 = 5 ∧ acceleratedOrbit 12 3194 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3194 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3194) = 3 ^ 5 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3194.1, data_12_3194.2]

/-- Complete interval computation for depth 12, residue 3195. -/
theorem bounds_12_3195 : exactInterval 12 3195 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3195 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3195) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3195 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3195 : oddCount 3195 12 = 6 ∧ acceleratedOrbit 12 3195 = 569 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3195 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3195) = 3 ^ 6 * m + 569 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3195.1, data_12_3195.2]

/-- Complete interval computation for depth 12, residue 3196. -/
theorem bounds_12_3196 : exactInterval 12 3196 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3196 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3196) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3196 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3196 : oddCount 3196 12 = 7 ∧ acceleratedOrbit 12 3196 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3196 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3196) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3196.1, data_12_3196.2]

/-- Complete interval computation for depth 12, residue 3197. -/
theorem bounds_12_3197 : exactInterval 12 3197 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3197 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3197) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3197 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3197 : oddCount 3197 12 = 7 ∧ acceleratedOrbit 12 3197 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3197 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3197) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3197.1, data_12_3197.2]

/-- Complete interval computation for depth 12, residue 3198. -/
theorem bounds_12_3198 : exactInterval 12 3198 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3198 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3198) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3198 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3198 : oddCount 3198 12 = 7 ∧ acceleratedOrbit 12 3198 = 1709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3198 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3198) = 3 ^ 7 * m + 1709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3198.1, data_12_3198.2]

/-- Complete interval computation for depth 12, residue 3199. -/
theorem bounds_12_3199 : exactInterval 12 3199 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3199 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3199) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3199 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3199 : oddCount 3199 12 = 10 ∧ acceleratedOrbit 12 3199 = 46133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3199 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3199) = 3 ^ 10 * m + 46133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3199.1, data_12_3199.2]

/-- Complete interval computation for depth 12, residue 3200. -/
theorem bounds_12_3200 : exactInterval 12 3200 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3200 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3200) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3200 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3200 : oddCount 3200 12 = 3 ∧ acceleratedOrbit 12 3200 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3200 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3200) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3200.1, data_12_3200.2]

/-- Complete interval computation for depth 12, residue 3201. -/
theorem bounds_12_3201 : exactInterval 12 3201 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3201 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3201) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3201 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3201 : oddCount 3201 12 = 7 ∧ acceleratedOrbit 12 3201 = 1711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3201 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3201) = 3 ^ 7 * m + 1711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3201.1, data_12_3201.2]

/-- Complete interval computation for depth 12, residue 3202. -/
theorem bounds_12_3202 : exactInterval 12 3202 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3202 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3202) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3202 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3202 : oddCount 3202 12 = 5 ∧ acceleratedOrbit 12 3202 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3202 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3202) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3202.1, data_12_3202.2]

/-- Complete interval computation for depth 12, residue 3203. -/
theorem bounds_12_3203 : exactInterval 12 3203 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3203 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3203) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3203 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3203 : oddCount 3203 12 = 5 ∧ acceleratedOrbit 12 3203 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3203 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3203) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3203.1, data_12_3203.2]

/-- Complete interval computation for depth 12, residue 3204. -/
theorem bounds_12_3204 : exactInterval 12 3204 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3204 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3204) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3204 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3204 : oddCount 3204 12 = 5 ∧ acceleratedOrbit 12 3204 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3204 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3204) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3204.1, data_12_3204.2]

/-- Complete interval computation for depth 12, residue 3205. -/
theorem bounds_12_3205 : exactInterval 12 3205 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3205 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3205) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3205 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3205 : oddCount 3205 12 = 5 ∧ acceleratedOrbit 12 3205 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3205 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3205) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3205.1, data_12_3205.2]

/-- Complete interval computation for depth 12, residue 3206. -/
theorem bounds_12_3206 : exactInterval 12 3206 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3206 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3206) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3206 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3206 : oddCount 3206 12 = 5 ∧ acceleratedOrbit 12 3206 = 191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3206 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3206) = 3 ^ 5 * m + 191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3206.1, data_12_3206.2]

/-- Complete interval computation for depth 12, residue 3207. -/
theorem bounds_12_3207 : exactInterval 12 3207 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3207 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3207) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3207 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3207 : oddCount 3207 12 = 7 ∧ acceleratedOrbit 12 3207 = 1714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3207 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3207) = 3 ^ 7 * m + 1714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3207.1, data_12_3207.2]

/-- Complete interval computation for depth 12, residue 3208. -/
theorem bounds_12_3208 : exactInterval 12 3208 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3208 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3208) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3208 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3208 : oddCount 3208 12 = 4 ∧ acceleratedOrbit 12 3208 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3208 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3208) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3208.1, data_12_3208.2]

/-- Complete interval computation for depth 12, residue 3209. -/
theorem bounds_12_3209 : exactInterval 12 3209 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3209 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3209) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3209 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3209 : oddCount 3209 12 = 9 ∧ acceleratedOrbit 12 3209 = 15430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3209 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3209) = 3 ^ 9 * m + 15430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3209.1, data_12_3209.2]

end Collatz.Research.StoppingAtlas.Batch0409
