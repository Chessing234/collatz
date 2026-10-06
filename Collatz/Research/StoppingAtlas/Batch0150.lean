import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0150

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1264. -/
theorem bounds_11_1264 : exactInterval 11 1264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1264 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1264) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1264 : oddCount 1264 11 = 5 ∧ acceleratedOrbit 11 1264 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1264 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1264) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1264.1, data_11_1264.2]

/-- Complete interval computation for depth 11, residue 1265. -/
theorem bounds_11_1265 : exactInterval 11 1265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1265 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1265) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1265 : oddCount 1265 11 = 5 ∧ acceleratedOrbit 11 1265 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1265 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1265) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1265.1, data_11_1265.2]

/-- Complete interval computation for depth 11, residue 1266. -/
theorem bounds_11_1266 : exactInterval 11 1266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1266 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1266) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1266 : oddCount 1266 11 = 6 ∧ acceleratedOrbit 11 1266 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1266 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1266) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1266.1, data_11_1266.2]

/-- Complete interval computation for depth 11, residue 1267. -/
theorem bounds_11_1267 : exactInterval 11 1267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1267 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1267) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1267 : oddCount 1267 11 = 6 ∧ acceleratedOrbit 11 1267 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1267 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1267) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1267.1, data_11_1267.2]

/-- Complete interval computation for depth 11, residue 1268. -/
theorem bounds_11_1268 : exactInterval 11 1268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1268 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1268) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1268 : oddCount 1268 11 = 5 ∧ acceleratedOrbit 11 1268 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1268 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1268) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1268.1, data_11_1268.2]

/-- Complete interval computation for depth 11, residue 1269. -/
theorem bounds_11_1269 : exactInterval 11 1269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1269 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1269) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1269 : oddCount 1269 11 = 5 ∧ acceleratedOrbit 11 1269 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1269 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1269) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1269.1, data_11_1269.2]

/-- Complete interval computation for depth 11, residue 1270. -/
theorem bounds_11_1270 : exactInterval 11 1270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1270 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1270) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1270 : oddCount 1270 11 = 5 ∧ acceleratedOrbit 11 1270 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1270 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1270) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1270.1, data_11_1270.2]

/-- Complete interval computation for depth 11, residue 1271. -/
theorem bounds_11_1271 : exactInterval 11 1271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1271 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1271) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1271 : oddCount 1271 11 = 5 ∧ acceleratedOrbit 11 1271 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1271 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1271) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1271.1, data_11_1271.2]

/-- Complete interval computation for depth 11, residue 1272. -/
theorem bounds_11_1272 : exactInterval 11 1272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1272 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1272) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1272 : oddCount 1272 11 = 7 ∧ acceleratedOrbit 11 1272 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1272 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1272) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1272.1, data_11_1272.2]

/-- Complete interval computation for depth 11, residue 1273. -/
theorem bounds_11_1273 : exactInterval 11 1273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1273 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1273) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1273 : oddCount 1273 11 = 6 ∧ acceleratedOrbit 11 1273 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1273 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1273) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1273.1, data_11_1273.2]

/-- Complete interval computation for depth 11, residue 1274. -/
theorem bounds_11_1274 : exactInterval 11 1274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1274 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1274) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1274 : oddCount 1274 11 = 7 ∧ acceleratedOrbit 11 1274 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1274 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1274) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1274.1, data_11_1274.2]

/-- Complete interval computation for depth 11, residue 1275. -/
theorem bounds_11_1275 : exactInterval 11 1275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1275 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1275) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1275 : oddCount 1275 11 = 8 ∧ acceleratedOrbit 11 1275 = 4090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1275 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1275) = 3 ^ 8 * m + 4090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1275.1, data_11_1275.2]

/-- Complete interval computation for depth 11, residue 1276. -/
theorem bounds_11_1276 : exactInterval 11 1276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1276 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1276) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1276 : oddCount 1276 11 = 7 ∧ acceleratedOrbit 11 1276 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1276 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1276) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1276.1, data_11_1276.2]

/-- Complete interval computation for depth 11, residue 1277. -/
theorem bounds_11_1277 : exactInterval 11 1277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1277 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1277) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1277 : oddCount 1277 11 = 7 ∧ acceleratedOrbit 11 1277 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1277 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1277) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1277.1, data_11_1277.2]

/-- Complete interval computation for depth 11, residue 1278. -/
theorem bounds_11_1278 : exactInterval 11 1278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1278 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1278) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1278 : oddCount 1278 11 = 9 ∧ acceleratedOrbit 11 1278 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1278 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1278) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1278.1, data_11_1278.2]

/-- Complete interval computation for depth 11, residue 1279. -/
theorem bounds_11_1279 : exactInterval 11 1279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1279 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1279) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1279 : oddCount 1279 11 = 9 ∧ acceleratedOrbit 11 1279 = 12302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1279 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1279) = 3 ^ 9 * m + 12302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1279.1, data_11_1279.2]

end Collatz.Research.StoppingAtlas.Batch0150
