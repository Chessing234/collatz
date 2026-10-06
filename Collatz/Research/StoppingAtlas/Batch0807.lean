import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0807

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5212. -/
theorem bounds_13_5212 : exactInterval 13 5212 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5212 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5212) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5212 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5212 : oddCount 5212 13 = 5 ∧ acceleratedOrbit 13 5212 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5212 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5212) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5212.1, data_13_5212.2]

/-- Complete interval computation for depth 13, residue 5213. -/
theorem bounds_13_5213 : exactInterval 13 5213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5213 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5213) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5213 : oddCount 5213 13 = 5 ∧ acceleratedOrbit 13 5213 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5213 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5213) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5213.1, data_13_5213.2]

/-- Complete interval computation for depth 13, residue 5214. -/
theorem bounds_13_5214 : exactInterval 13 5214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5214 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5214) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5214 : oddCount 5214 13 = 8 ∧ acceleratedOrbit 13 5214 = 4178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5214 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5214) = 3 ^ 8 * m + 4178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5214.1, data_13_5214.2]

/-- Complete interval computation for depth 13, residue 5215. -/
theorem bounds_13_5215 : exactInterval 13 5215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5215 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5215) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5215 : oddCount 5215 13 = 8 ∧ acceleratedOrbit 13 5215 = 4178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5215 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5215) = 3 ^ 8 * m + 4178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5215.1, data_13_5215.2]

/-- Complete interval computation for depth 13, residue 5216. -/
theorem bounds_13_5216 : exactInterval 13 5216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5216 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5216) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5216 : oddCount 5216 13 = 4 ∧ acceleratedOrbit 13 5216 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5216 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5216) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5216.1, data_13_5216.2]

/-- Complete interval computation for depth 13, residue 5217. -/
theorem bounds_13_5217 : exactInterval 13 5217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5217 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5217) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5217 : oddCount 5217 13 = 7 ∧ acceleratedOrbit 13 5217 = 1394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5217 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5217) = 3 ^ 7 * m + 1394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5217.1, data_13_5217.2]

/-- Complete interval computation for depth 13, residue 5218. -/
theorem bounds_13_5218 : exactInterval 13 5218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5218 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5218) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5218 : oddCount 5218 13 = 7 ∧ acceleratedOrbit 13 5218 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5218 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5218) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5218.1, data_13_5218.2]

/-- Complete interval computation for depth 13, residue 5219. -/
theorem bounds_13_5219 : exactInterval 13 5219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5219 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5219) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5219 : oddCount 5219 13 = 7 ∧ acceleratedOrbit 13 5219 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5219 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5219) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5219.1, data_13_5219.2]

/-- Complete interval computation for depth 13, residue 5220. -/
theorem bounds_13_5220 : exactInterval 13 5220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5220 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5220) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5220 : oddCount 5220 13 = 7 ∧ acceleratedOrbit 13 5220 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5220 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5220) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5220.1, data_13_5220.2]

/-- Complete interval computation for depth 13, residue 5221. -/
theorem bounds_13_5221 : exactInterval 13 5221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5221 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5221) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5221 : oddCount 5221 13 = 7 ∧ acceleratedOrbit 13 5221 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5221 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5221) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5221.1, data_13_5221.2]

/-- Complete interval computation for depth 13, residue 5222. -/
theorem bounds_13_5222 : exactInterval 13 5222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5222 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5222) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5222 : oddCount 5222 13 = 7 ∧ acceleratedOrbit 13 5222 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5222 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5222) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5222.1, data_13_5222.2]

/-- Complete interval computation for depth 13, residue 5223. -/
theorem bounds_13_5223 : exactInterval 13 5223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5223 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5223) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5223 : oddCount 5223 13 = 10 ∧ acceleratedOrbit 13 5223 = 37658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5223 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5223) = 3 ^ 10 * m + 37658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5223.1, data_13_5223.2]

/-- Complete interval computation for depth 13, residue 5224. -/
theorem bounds_13_5224 : exactInterval 13 5224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5224 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5224) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5224 : oddCount 5224 13 = 4 ∧ acceleratedOrbit 13 5224 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5224 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5224) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5224.1, data_13_5224.2]

/-- Complete interval computation for depth 13, residue 5225. -/
theorem bounds_13_5225 : exactInterval 13 5225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5225 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5225) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5225 : oddCount 5225 13 = 8 ∧ acceleratedOrbit 13 5225 = 4187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5225 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5225) = 3 ^ 8 * m + 4187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5225.1, data_13_5225.2]

/-- Complete interval computation for depth 13, residue 5226. -/
theorem bounds_13_5226 : exactInterval 13 5226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5226 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5226) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5226 : oddCount 5226 13 = 4 ∧ acceleratedOrbit 13 5226 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5226 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5226) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5226.1, data_13_5226.2]

end Collatz.Research.StoppingAtlas.Batch0807
