import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0148

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1233. -/
theorem bounds_11_1233 : exactInterval 11 1233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1233 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1233) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1233 : oddCount 1233 11 = 7 ∧ acceleratedOrbit 11 1233 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1233 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1233) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1233.1, data_11_1233.2]

/-- Complete interval computation for depth 11, residue 1234. -/
theorem bounds_11_1234 : exactInterval 11 1234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1234 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1234) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1234 : oddCount 1234 11 = 7 ∧ acceleratedOrbit 11 1234 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1234 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1234) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1234.1, data_11_1234.2]

/-- Complete interval computation for depth 11, residue 1235. -/
theorem bounds_11_1235 : exactInterval 11 1235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1235 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1235) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1235 : oddCount 1235 11 = 7 ∧ acceleratedOrbit 11 1235 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1235 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1235) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1235.1, data_11_1235.2]

/-- Complete interval computation for depth 11, residue 1236. -/
theorem bounds_11_1236 : exactInterval 11 1236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1236 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1236) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1236 : oddCount 1236 11 = 3 ∧ acceleratedOrbit 11 1236 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1236 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1236) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1236.1, data_11_1236.2]

/-- Complete interval computation for depth 11, residue 1237. -/
theorem bounds_11_1237 : exactInterval 11 1237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1237 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1237) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1237 : oddCount 1237 11 = 3 ∧ acceleratedOrbit 11 1237 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1237 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1237) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1237.1, data_11_1237.2]

/-- Complete interval computation for depth 11, residue 1238. -/
theorem bounds_11_1238 : exactInterval 11 1238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1238 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1238) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1238 : oddCount 1238 11 = 6 ∧ acceleratedOrbit 11 1238 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1238 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1238) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1238.1, data_11_1238.2]

/-- Complete interval computation for depth 11, residue 1239. -/
theorem bounds_11_1239 : exactInterval 11 1239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1239 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1239) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1239 : oddCount 1239 11 = 6 ∧ acceleratedOrbit 11 1239 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1239 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1239) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1239.1, data_11_1239.2]

/-- Complete interval computation for depth 11, residue 1240. -/
theorem bounds_11_1240 : exactInterval 11 1240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1240 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1240) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1240 : oddCount 1240 11 = 6 ∧ acceleratedOrbit 11 1240 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1240 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1240) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1240.1, data_11_1240.2]

/-- Complete interval computation for depth 11, residue 1241. -/
theorem bounds_11_1241 : exactInterval 11 1241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1241 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1241) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1241 : oddCount 1241 11 = 5 ∧ acceleratedOrbit 11 1241 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1241 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1241) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1241.1, data_11_1241.2]

/-- Complete interval computation for depth 11, residue 1242. -/
theorem bounds_11_1242 : exactInterval 11 1242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1242 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1242) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1242 : oddCount 1242 11 = 6 ∧ acceleratedOrbit 11 1242 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1242 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1242) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1242.1, data_11_1242.2]

/-- Complete interval computation for depth 11, residue 1243. -/
theorem bounds_11_1243 : exactInterval 11 1243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1243 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1243) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1243 : oddCount 1243 11 = 6 ∧ acceleratedOrbit 11 1243 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1243 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1243) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1243.1, data_11_1243.2]

/-- Complete interval computation for depth 11, residue 1244. -/
theorem bounds_11_1244 : exactInterval 11 1244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1244 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1244) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1244 : oddCount 1244 11 = 6 ∧ acceleratedOrbit 11 1244 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1244 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1244) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1244.1, data_11_1244.2]

/-- Complete interval computation for depth 11, residue 1245. -/
theorem bounds_11_1245 : exactInterval 11 1245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1245 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1245) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1245 : oddCount 1245 11 = 6 ∧ acceleratedOrbit 11 1245 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1245 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1245) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1245.1, data_11_1245.2]

/-- Complete interval computation for depth 11, residue 1246. -/
theorem bounds_11_1246 : exactInterval 11 1246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1246 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1246) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1246 : oddCount 1246 11 = 7 ∧ acceleratedOrbit 11 1246 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1246 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1246) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1246.1, data_11_1246.2]

/-- Complete interval computation for depth 11, residue 1247. -/
theorem bounds_11_1247 : exactInterval 11 1247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1247 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1247) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1247 : oddCount 1247 11 = 7 ∧ acceleratedOrbit 11 1247 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1247 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1247) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1247.1, data_11_1247.2]

/-- Complete interval computation for depth 11, residue 1248. -/
theorem bounds_11_1248 : exactInterval 11 1248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1248 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1248) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1248 : oddCount 1248 11 = 5 ∧ acceleratedOrbit 11 1248 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1248 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1248) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1248.1, data_11_1248.2]

end Collatz.Research.StoppingAtlas.Batch0148
