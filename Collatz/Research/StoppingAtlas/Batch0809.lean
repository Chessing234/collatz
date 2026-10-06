import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0809

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5242. -/
theorem bounds_13_5242 : exactInterval 13 5242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5242 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5242) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5242 : oddCount 5242 13 = 7 ∧ acceleratedOrbit 13 5242 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5242 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5242) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5242.1, data_13_5242.2]

/-- Complete interval computation for depth 13, residue 5243. -/
theorem bounds_13_5243 : exactInterval 13 5243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5243 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5243) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5243 : oddCount 5243 13 = 8 ∧ acceleratedOrbit 13 5243 = 4202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5243 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5243) = 3 ^ 8 * m + 4202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5243.1, data_13_5243.2]

/-- Complete interval computation for depth 13, residue 5244. -/
theorem bounds_13_5244 : exactInterval 13 5244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5244 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5244) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5244 : oddCount 5244 13 = 6 ∧ acceleratedOrbit 13 5244 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5244 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5244) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5244.1, data_13_5244.2]

/-- Complete interval computation for depth 13, residue 5245. -/
theorem bounds_13_5245 : exactInterval 13 5245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5245 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5245) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5245 : oddCount 5245 13 = 6 ∧ acceleratedOrbit 13 5245 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5245 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5245) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5245.1, data_13_5245.2]

/-- Complete interval computation for depth 13, residue 5246. -/
theorem bounds_13_5246 : exactInterval 13 5246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5246 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5246) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5246 : oddCount 5246 13 = 6 ∧ acceleratedOrbit 13 5246 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5246 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5246) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5246.1, data_13_5246.2]

/-- Complete interval computation for depth 13, residue 5247. -/
theorem bounds_13_5247 : exactInterval 13 5247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5247 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5247) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5247 : oddCount 5247 13 = 10 ∧ acceleratedOrbit 13 5247 = 37829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5247 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5247) = 3 ^ 10 * m + 37829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5247.1, data_13_5247.2]

/-- Complete interval computation for depth 13, residue 5248. -/
theorem bounds_13_5248 : exactInterval 13 5248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5248 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5248) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5248 : oddCount 5248 13 = 5 ∧ acceleratedOrbit 13 5248 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5248 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5248) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5248.1, data_13_5248.2]

/-- Complete interval computation for depth 13, residue 5249. -/
theorem bounds_13_5249 : exactInterval 13 5249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5249 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5249) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5249 : oddCount 5249 13 = 8 ∧ acceleratedOrbit 13 5249 = 4207 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5249 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5249) = 3 ^ 8 * m + 4207 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5249.1, data_13_5249.2]

/-- Complete interval computation for depth 13, residue 5250. -/
theorem bounds_13_5250 : exactInterval 13 5250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5250 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5250) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5250 : oddCount 5250 13 = 4 ∧ acceleratedOrbit 13 5250 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5250 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5250) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5250.1, data_13_5250.2]

/-- Complete interval computation for depth 13, residue 5251. -/
theorem bounds_13_5251 : exactInterval 13 5251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5251 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5251) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5251 : oddCount 5251 13 = 4 ∧ acceleratedOrbit 13 5251 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5251 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5251) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5251.1, data_13_5251.2]

/-- Complete interval computation for depth 13, residue 5252. -/
theorem bounds_13_5252 : exactInterval 13 5252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5252 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5252) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5252 : oddCount 5252 13 = 4 ∧ acceleratedOrbit 13 5252 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5252 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5252) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5252.1, data_13_5252.2]

/-- Complete interval computation for depth 13, residue 5253. -/
theorem bounds_13_5253 : exactInterval 13 5253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5253 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5253) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5253 : oddCount 5253 13 = 4 ∧ acceleratedOrbit 13 5253 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5253 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5253) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5253.1, data_13_5253.2]

/-- Complete interval computation for depth 13, residue 5254. -/
theorem bounds_13_5254 : exactInterval 13 5254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5254 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5254) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5254 : oddCount 5254 13 = 4 ∧ acceleratedOrbit 13 5254 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5254 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5254) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5254.1, data_13_5254.2]

/-- Complete interval computation for depth 13, residue 5255. -/
theorem bounds_13_5255 : exactInterval 13 5255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5255 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5255) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5255 : oddCount 5255 13 = 9 ∧ acceleratedOrbit 13 5255 = 12635 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5255 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5255) = 3 ^ 9 * m + 12635 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5255.1, data_13_5255.2]

/-- Complete interval computation for depth 13, residue 5256. -/
theorem bounds_13_5256 : exactInterval 13 5256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5256 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5256) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5256 : oddCount 5256 13 = 5 ∧ acceleratedOrbit 13 5256 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5256 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5256) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5256.1, data_13_5256.2]

/-- Complete interval computation for depth 13, residue 5257. -/
theorem bounds_13_5257 : exactInterval 13 5257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5257 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5257) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5257 : oddCount 5257 13 = 11 ∧ acceleratedOrbit 13 5257 = 113723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5257 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5257) = 3 ^ 11 * m + 113723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5257.1, data_13_5257.2]

end Collatz.Research.StoppingAtlas.Batch0809
