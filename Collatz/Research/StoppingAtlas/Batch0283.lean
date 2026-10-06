import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0283

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1259. -/
theorem bounds_12_1259 : exactInterval 12 1259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1259 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1259) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1259 : oddCount 1259 12 = 8 ∧ acceleratedOrbit 12 1259 = 2020 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1259 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1259) = 3 ^ 8 * m + 2020 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1259.1, data_12_1259.2]

/-- Complete interval computation for depth 12, residue 1260. -/
theorem bounds_12_1260 : exactInterval 12 1260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1260 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1260) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1260 : oddCount 1260 12 = 4 ∧ acceleratedOrbit 12 1260 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1260 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1260) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1260.1, data_12_1260.2]

/-- Complete interval computation for depth 12, residue 1261. -/
theorem bounds_12_1261 : exactInterval 12 1261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1261 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1261) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1261 : oddCount 1261 12 = 4 ∧ acceleratedOrbit 12 1261 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1261 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1261) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1261.1, data_12_1261.2]

/-- Complete interval computation for depth 12, residue 1262. -/
theorem bounds_12_1262 : exactInterval 12 1262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1262 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1262) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1262 : oddCount 1262 12 = 4 ∧ acceleratedOrbit 12 1262 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1262 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1262) = 3 ^ 4 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1262.1, data_12_1262.2]

/-- Complete interval computation for depth 12, residue 1263. -/
theorem bounds_12_1263 : exactInterval 12 1263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1263 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1263) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1263 : oddCount 1263 12 = 11 ∧ acceleratedOrbit 12 1263 = 54674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1263 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1263) = 3 ^ 11 * m + 54674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1263.1, data_12_1263.2]

/-- Complete interval computation for depth 12, residue 1264. -/
theorem bounds_12_1264 : exactInterval 12 1264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1264 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1264) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1264 : oddCount 1264 12 = 5 ∧ acceleratedOrbit 12 1264 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1264 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1264) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1264.1, data_12_1264.2]

/-- Complete interval computation for depth 12, residue 1265. -/
theorem bounds_12_1265 : exactInterval 12 1265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1265 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1265) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1265 : oddCount 1265 12 = 5 ∧ acceleratedOrbit 12 1265 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1265 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1265) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1265.1, data_12_1265.2]

/-- Complete interval computation for depth 12, residue 1266. -/
theorem bounds_12_1266 : exactInterval 12 1266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1266 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1266) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1266 : oddCount 1266 12 = 6 ∧ acceleratedOrbit 12 1266 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1266 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1266) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1266.1, data_12_1266.2]

/-- Complete interval computation for depth 12, residue 1267. -/
theorem bounds_12_1267 : exactInterval 12 1267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1267 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1267) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1267 : oddCount 1267 12 = 6 ∧ acceleratedOrbit 12 1267 = 226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1267 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1267) = 3 ^ 6 * m + 226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1267.1, data_12_1267.2]

/-- Complete interval computation for depth 12, residue 1268. -/
theorem bounds_12_1268 : exactInterval 12 1268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1268 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1268) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1268 : oddCount 1268 12 = 5 ∧ acceleratedOrbit 12 1268 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1268 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1268) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1268.1, data_12_1268.2]

/-- Complete interval computation for depth 12, residue 1269. -/
theorem bounds_12_1269 : exactInterval 12 1269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1269 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1269) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1269 : oddCount 1269 12 = 5 ∧ acceleratedOrbit 12 1269 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1269 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1269) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1269.1, data_12_1269.2]

/-- Complete interval computation for depth 12, residue 1270. -/
theorem bounds_12_1270 : exactInterval 12 1270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1270 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1270) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1270 : oddCount 1270 12 = 6 ∧ acceleratedOrbit 12 1270 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1270 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1270) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1270.1, data_12_1270.2]

/-- Complete interval computation for depth 12, residue 1271. -/
theorem bounds_12_1271 : exactInterval 12 1271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1271 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1271) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1271 : oddCount 1271 12 = 6 ∧ acceleratedOrbit 12 1271 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1271 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1271) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1271.1, data_12_1271.2]

/-- Complete interval computation for depth 12, residue 1272. -/
theorem bounds_12_1272 : exactInterval 12 1272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1272 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1272) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1272 : oddCount 1272 12 = 8 ∧ acceleratedOrbit 12 1272 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1272 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1272) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1272.1, data_12_1272.2]

/-- Complete interval computation for depth 12, residue 1273. -/
theorem bounds_12_1273 : exactInterval 12 1273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1273 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1273) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1273 : oddCount 1273 12 = 6 ∧ acceleratedOrbit 12 1273 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1273 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1273) = 3 ^ 6 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1273.1, data_12_1273.2]

end Collatz.Research.StoppingAtlas.Batch0283
