import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0284

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1274. -/
theorem bounds_12_1274 : exactInterval 12 1274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1274 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1274) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1274 : oddCount 1274 12 = 8 ∧ acceleratedOrbit 12 1274 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1274 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1274) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1274.1, data_12_1274.2]

/-- Complete interval computation for depth 12, residue 1275. -/
theorem bounds_12_1275 : exactInterval 12 1275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1275 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1275) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1275 : oddCount 1275 12 = 8 ∧ acceleratedOrbit 12 1275 = 2045 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1275 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1275) = 3 ^ 8 * m + 2045 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1275.1, data_12_1275.2]

/-- Complete interval computation for depth 12, residue 1276. -/
theorem bounds_12_1276 : exactInterval 12 1276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1276 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1276) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1276 : oddCount 1276 12 = 8 ∧ acceleratedOrbit 12 1276 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1276 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1276) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1276.1, data_12_1276.2]

/-- Complete interval computation for depth 12, residue 1277. -/
theorem bounds_12_1277 : exactInterval 12 1277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1277 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1277) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1277 : oddCount 1277 12 = 8 ∧ acceleratedOrbit 12 1277 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1277 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1277) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1277.1, data_12_1277.2]

/-- Complete interval computation for depth 12, residue 1278. -/
theorem bounds_12_1278 : exactInterval 12 1278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1278 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1278) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1278 : oddCount 1278 12 = 9 ∧ acceleratedOrbit 12 1278 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1278 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1278) = 3 ^ 9 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1278.1, data_12_1278.2]

/-- Complete interval computation for depth 12, residue 1279. -/
theorem bounds_12_1279 : exactInterval 12 1279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1279 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1279) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1279 : oddCount 1279 12 = 9 ∧ acceleratedOrbit 12 1279 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1279 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1279) = 3 ^ 9 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1279.1, data_12_1279.2]

/-- Complete interval computation for depth 12, residue 1280. -/
theorem bounds_12_1280 : exactInterval 12 1280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1280 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1280) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1280 : oddCount 1280 12 = 1 ∧ acceleratedOrbit 12 1280 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1280 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1280) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1280.1, data_12_1280.2]

/-- Complete interval computation for depth 12, residue 1281. -/
theorem bounds_12_1281 : exactInterval 12 1281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1281 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1281) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1281 : oddCount 1281 12 = 6 ∧ acceleratedOrbit 12 1281 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1281 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1281) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1281.1, data_12_1281.2]

/-- Complete interval computation for depth 12, residue 1282. -/
theorem bounds_12_1282 : exactInterval 12 1282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1282 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1282) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1282 : oddCount 1282 12 = 7 ∧ acceleratedOrbit 12 1282 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1282 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1282) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1282.1, data_12_1282.2]

/-- Complete interval computation for depth 12, residue 1283. -/
theorem bounds_12_1283 : exactInterval 12 1283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1283 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1283) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1283 : oddCount 1283 12 = 7 ∧ acceleratedOrbit 12 1283 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1283 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1283) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1283.1, data_12_1283.2]

/-- Complete interval computation for depth 12, residue 1284. -/
theorem bounds_12_1284 : exactInterval 12 1284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1284 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1284) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1284 : oddCount 1284 12 = 4 ∧ acceleratedOrbit 12 1284 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1284 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1284) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1284.1, data_12_1284.2]

/-- Complete interval computation for depth 12, residue 1285. -/
theorem bounds_12_1285 : exactInterval 12 1285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1285 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1285) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1285 : oddCount 1285 12 = 4 ∧ acceleratedOrbit 12 1285 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1285 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1285) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1285.1, data_12_1285.2]

/-- Complete interval computation for depth 12, residue 1286. -/
theorem bounds_12_1286 : exactInterval 12 1286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1286 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1286) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1286 : oddCount 1286 12 = 4 ∧ acceleratedOrbit 12 1286 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1286 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1286) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1286.1, data_12_1286.2]

/-- Complete interval computation for depth 12, residue 1287. -/
theorem bounds_12_1287 : exactInterval 12 1287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1287 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1287) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1287 : oddCount 1287 12 = 8 ∧ acceleratedOrbit 12 1287 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1287 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1287) = 3 ^ 8 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1287.1, data_12_1287.2]

/-- Complete interval computation for depth 12, residue 1288. -/
theorem bounds_12_1288 : exactInterval 12 1288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1288 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1288) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1288 : oddCount 1288 12 = 6 ∧ acceleratedOrbit 12 1288 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1288 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1288) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1288.1, data_12_1288.2]

/-- Complete interval computation for depth 12, residue 1289. -/
theorem bounds_12_1289 : exactInterval 12 1289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1289 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1289) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1289 : oddCount 1289 12 = 8 ∧ acceleratedOrbit 12 1289 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1289 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1289) = 3 ^ 8 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1289.1, data_12_1289.2]

end Collatz.Research.StoppingAtlas.Batch0284
