import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0550

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1264. -/
theorem bounds_13_1264 : exactInterval 13 1264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1264 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1264) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1264 : oddCount 1264 13 = 5 ∧ acceleratedOrbit 13 1264 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1264 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1264) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1264.1, data_13_1264.2]

/-- Complete interval computation for depth 13, residue 1265. -/
theorem bounds_13_1265 : exactInterval 13 1265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1265 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1265) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1265 : oddCount 1265 13 = 5 ∧ acceleratedOrbit 13 1265 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1265 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1265) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1265.1, data_13_1265.2]

/-- Complete interval computation for depth 13, residue 1266. -/
theorem bounds_13_1266 : exactInterval 13 1266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1266 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1266) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1266 : oddCount 1266 13 = 6 ∧ acceleratedOrbit 13 1266 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1266 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1266) = 3 ^ 6 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1266.1, data_13_1266.2]

/-- Complete interval computation for depth 13, residue 1267. -/
theorem bounds_13_1267 : exactInterval 13 1267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1267 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1267) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1267 : oddCount 1267 13 = 6 ∧ acceleratedOrbit 13 1267 = 113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1267 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1267) = 3 ^ 6 * m + 113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1267.1, data_13_1267.2]

/-- Complete interval computation for depth 13, residue 1268. -/
theorem bounds_13_1268 : exactInterval 13 1268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1268 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1268) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1268 : oddCount 1268 13 = 5 ∧ acceleratedOrbit 13 1268 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1268 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1268) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1268.1, data_13_1268.2]

/-- Complete interval computation for depth 13, residue 1269. -/
theorem bounds_13_1269 : exactInterval 13 1269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1269 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1269) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1269 : oddCount 1269 13 = 5 ∧ acceleratedOrbit 13 1269 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1269 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1269) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1269.1, data_13_1269.2]

/-- Complete interval computation for depth 13, residue 1270. -/
theorem bounds_13_1270 : exactInterval 13 1270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1270 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1270) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1270 : oddCount 1270 13 = 7 ∧ acceleratedOrbit 13 1270 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1270 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1270) = 3 ^ 7 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1270.1, data_13_1270.2]

/-- Complete interval computation for depth 13, residue 1271. -/
theorem bounds_13_1271 : exactInterval 13 1271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1271 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1271) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1271 : oddCount 1271 13 = 7 ∧ acceleratedOrbit 13 1271 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1271 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1271) = 3 ^ 7 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1271.1, data_13_1271.2]

/-- Complete interval computation for depth 13, residue 1272. -/
theorem bounds_13_1272 : exactInterval 13 1272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1272 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1272) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1272 : oddCount 1272 13 = 9 ∧ acceleratedOrbit 13 1272 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1272 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1272) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1272.1, data_13_1272.2]

/-- Complete interval computation for depth 13, residue 1273. -/
theorem bounds_13_1273 : exactInterval 13 1273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1273 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1273) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1273 : oddCount 1273 13 = 7 ∧ acceleratedOrbit 13 1273 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1273 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1273) = 3 ^ 7 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1273.1, data_13_1273.2]

/-- Complete interval computation for depth 13, residue 1274. -/
theorem bounds_13_1274 : exactInterval 13 1274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1274 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1274) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1274 : oddCount 1274 13 = 9 ∧ acceleratedOrbit 13 1274 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1274 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1274) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1274.1, data_13_1274.2]

/-- Complete interval computation for depth 13, residue 1275. -/
theorem bounds_13_1275 : exactInterval 13 1275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1275 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1275) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1275 : oddCount 1275 13 = 9 ∧ acceleratedOrbit 13 1275 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1275 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1275) = 3 ^ 9 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1275.1, data_13_1275.2]

/-- Complete interval computation for depth 13, residue 1276. -/
theorem bounds_13_1276 : exactInterval 13 1276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1276 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1276) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1276 : oddCount 1276 13 = 9 ∧ acceleratedOrbit 13 1276 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1276 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1276) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1276.1, data_13_1276.2]

/-- Complete interval computation for depth 13, residue 1277. -/
theorem bounds_13_1277 : exactInterval 13 1277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1277 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1277) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1277 : oddCount 1277 13 = 9 ∧ acceleratedOrbit 13 1277 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1277 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1277) = 3 ^ 9 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1277.1, data_13_1277.2]

/-- Complete interval computation for depth 13, residue 1278. -/
theorem bounds_13_1278 : exactInterval 13 1278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1278 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1278) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1278 : oddCount 1278 13 = 10 ∧ acceleratedOrbit 13 1278 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1278 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1278) = 3 ^ 10 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1278.1, data_13_1278.2]

/-- Complete interval computation for depth 13, residue 1279. -/
theorem bounds_13_1279 : exactInterval 13 1279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1279 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1279) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1279 : oddCount 1279 13 = 10 ∧ acceleratedOrbit 13 1279 = 9227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1279 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1279) = 3 ^ 10 * m + 9227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1279.1, data_13_1279.2]

end Collatz.Research.StoppingAtlas.Batch0550
