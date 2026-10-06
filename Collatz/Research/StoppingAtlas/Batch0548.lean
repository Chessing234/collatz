import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0548

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1233. -/
theorem bounds_13_1233 : exactInterval 13 1233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1233 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1233) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1233 : oddCount 1233 13 = 8 ∧ acceleratedOrbit 13 1233 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1233 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1233) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1233.1, data_13_1233.2]

/-- Complete interval computation for depth 13, residue 1234. -/
theorem bounds_13_1234 : exactInterval 13 1234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1234 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1234) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1234 : oddCount 1234 13 = 8 ∧ acceleratedOrbit 13 1234 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1234 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1234) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1234.1, data_13_1234.2]

/-- Complete interval computation for depth 13, residue 1235. -/
theorem bounds_13_1235 : exactInterval 13 1235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1235 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1235) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1235 : oddCount 1235 13 = 8 ∧ acceleratedOrbit 13 1235 = 992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1235 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1235) = 3 ^ 8 * m + 992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1235.1, data_13_1235.2]

/-- Complete interval computation for depth 13, residue 1236. -/
theorem bounds_13_1236 : exactInterval 13 1236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1236 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1236) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1236 : oddCount 1236 13 = 4 ∧ acceleratedOrbit 13 1236 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1236 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1236) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1236.1, data_13_1236.2]

/-- Complete interval computation for depth 13, residue 1237. -/
theorem bounds_13_1237 : exactInterval 13 1237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1237 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1237) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1237 : oddCount 1237 13 = 4 ∧ acceleratedOrbit 13 1237 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1237 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1237) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1237.1, data_13_1237.2]

/-- Complete interval computation for depth 13, residue 1238. -/
theorem bounds_13_1238 : exactInterval 13 1238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1238 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1238) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1238 : oddCount 1238 13 = 7 ∧ acceleratedOrbit 13 1238 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1238 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1238) = 3 ^ 7 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1238.1, data_13_1238.2]

/-- Complete interval computation for depth 13, residue 1239. -/
theorem bounds_13_1239 : exactInterval 13 1239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1239 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1239) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1239 : oddCount 1239 13 = 7 ∧ acceleratedOrbit 13 1239 = 332 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1239 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1239) = 3 ^ 7 * m + 332 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1239.1, data_13_1239.2]

/-- Complete interval computation for depth 13, residue 1240. -/
theorem bounds_13_1240 : exactInterval 13 1240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1240 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1240) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1240 : oddCount 1240 13 = 7 ∧ acceleratedOrbit 13 1240 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1240 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1240) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1240.1, data_13_1240.2]

/-- Complete interval computation for depth 13, residue 1241. -/
theorem bounds_13_1241 : exactInterval 13 1241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1241 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1241) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1241 : oddCount 1241 13 = 5 ∧ acceleratedOrbit 13 1241 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1241 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1241) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1241.1, data_13_1241.2]

/-- Complete interval computation for depth 13, residue 1242. -/
theorem bounds_13_1242 : exactInterval 13 1242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1242 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1242) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1242 : oddCount 1242 13 = 7 ∧ acceleratedOrbit 13 1242 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1242 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1242) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1242.1, data_13_1242.2]

/-- Complete interval computation for depth 13, residue 1243. -/
theorem bounds_13_1243 : exactInterval 13 1243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1243 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1243) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1243 : oddCount 1243 13 = 8 ∧ acceleratedOrbit 13 1243 = 998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1243 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1243) = 3 ^ 8 * m + 998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1243.1, data_13_1243.2]

/-- Complete interval computation for depth 13, residue 1244. -/
theorem bounds_13_1244 : exactInterval 13 1244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1244 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1244) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1244 : oddCount 1244 13 = 7 ∧ acceleratedOrbit 13 1244 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1244 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1244) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1244.1, data_13_1244.2]

/-- Complete interval computation for depth 13, residue 1245. -/
theorem bounds_13_1245 : exactInterval 13 1245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1245 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1245) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1245 : oddCount 1245 13 = 7 ∧ acceleratedOrbit 13 1245 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1245 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1245) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1245.1, data_13_1245.2]

/-- Complete interval computation for depth 13, residue 1246. -/
theorem bounds_13_1246 : exactInterval 13 1246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1246 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1246) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1246 : oddCount 1246 13 = 8 ∧ acceleratedOrbit 13 1246 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1246 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1246) = 3 ^ 8 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1246.1, data_13_1246.2]

/-- Complete interval computation for depth 13, residue 1247. -/
theorem bounds_13_1247 : exactInterval 13 1247 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1247 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1247) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1247 : oddCount 1247 13 = 8 ∧ acceleratedOrbit 13 1247 = 1000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1247 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1247) = 3 ^ 8 * m + 1000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1247.1, data_13_1247.2]

/-- Complete interval computation for depth 13, residue 1248. -/
theorem bounds_13_1248 : exactInterval 13 1248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1248 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1248) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1248 : oddCount 1248 13 = 5 ∧ acceleratedOrbit 13 1248 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1248 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1248) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1248.1, data_13_1248.2]

end Collatz.Research.StoppingAtlas.Batch0548
