import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0549

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1249. -/
theorem bounds_13_1249 : exactInterval 13 1249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1249 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1249) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1249 : oddCount 1249 13 = 9 ∧ acceleratedOrbit 13 1249 = 3007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1249 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1249) = 3 ^ 9 * m + 3007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1249.1, data_13_1249.2]

/-- Complete interval computation for depth 13, residue 1250. -/
theorem bounds_13_1250 : exactInterval 13 1250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1250 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1250) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1250 : oddCount 1250 13 = 4 ∧ acceleratedOrbit 13 1250 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1250 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1250) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1250.1, data_13_1250.2]

/-- Complete interval computation for depth 13, residue 1251. -/
theorem bounds_13_1251 : exactInterval 13 1251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1251 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1251) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1251 : oddCount 1251 13 = 4 ∧ acceleratedOrbit 13 1251 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1251 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1251) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1251.1, data_13_1251.2]

/-- Complete interval computation for depth 13, residue 1252. -/
theorem bounds_13_1252 : exactInterval 13 1252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1252 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1252) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1252 : oddCount 1252 13 = 7 ∧ acceleratedOrbit 13 1252 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1252 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1252) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1252.1, data_13_1252.2]

/-- Complete interval computation for depth 13, residue 1253. -/
theorem bounds_13_1253 : exactInterval 13 1253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1253 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1253) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1253 : oddCount 1253 13 = 7 ∧ acceleratedOrbit 13 1253 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1253 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1253) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1253.1, data_13_1253.2]

/-- Complete interval computation for depth 13, residue 1254. -/
theorem bounds_13_1254 : exactInterval 13 1254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1254 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1254) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1254 : oddCount 1254 13 = 7 ∧ acceleratedOrbit 13 1254 = 337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1254 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1254) = 3 ^ 7 * m + 337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1254.1, data_13_1254.2]

/-- Complete interval computation for depth 13, residue 1255. -/
theorem bounds_13_1255 : exactInterval 13 1255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1255 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1255) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1255 : oddCount 1255 13 = 9 ∧ acceleratedOrbit 13 1255 = 3019 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1255 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1255) = 3 ^ 9 * m + 3019 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1255.1, data_13_1255.2]

/-- Complete interval computation for depth 13, residue 1256. -/
theorem bounds_13_1256 : exactInterval 13 1256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1256 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1256) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1256 : oddCount 1256 13 = 5 ∧ acceleratedOrbit 13 1256 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1256 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1256) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1256.1, data_13_1256.2]

/-- Complete interval computation for depth 13, residue 1257. -/
theorem bounds_13_1257 : exactInterval 13 1257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1257 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1257) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1257 : oddCount 1257 13 = 6 ∧ acceleratedOrbit 13 1257 = 112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1257 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1257) = 3 ^ 6 * m + 112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1257.1, data_13_1257.2]

/-- Complete interval computation for depth 13, residue 1258. -/
theorem bounds_13_1258 : exactInterval 13 1258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1258 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1258) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1258 : oddCount 1258 13 = 5 ∧ acceleratedOrbit 13 1258 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1258 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1258) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1258.1, data_13_1258.2]

/-- Complete interval computation for depth 13, residue 1259. -/
theorem bounds_13_1259 : exactInterval 13 1259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1259 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1259) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1259 : oddCount 1259 13 = 8 ∧ acceleratedOrbit 13 1259 = 1010 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1259 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1259) = 3 ^ 8 * m + 1010 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1259.1, data_13_1259.2]

/-- Complete interval computation for depth 13, residue 1260. -/
theorem bounds_13_1260 : exactInterval 13 1260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1260 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1260) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1260 : oddCount 1260 13 = 5 ∧ acceleratedOrbit 13 1260 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1260 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1260) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1260.1, data_13_1260.2]

/-- Complete interval computation for depth 13, residue 1261. -/
theorem bounds_13_1261 : exactInterval 13 1261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1261 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1261) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1261 : oddCount 1261 13 = 5 ∧ acceleratedOrbit 13 1261 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1261 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1261) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1261.1, data_13_1261.2]

/-- Complete interval computation for depth 13, residue 1262. -/
theorem bounds_13_1262 : exactInterval 13 1262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1262 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1262) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1262 : oddCount 1262 13 = 5 ∧ acceleratedOrbit 13 1262 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1262 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1262) = 3 ^ 5 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1262.1, data_13_1262.2]

/-- Complete interval computation for depth 13, residue 1263. -/
theorem bounds_13_1263 : exactInterval 13 1263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1263 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1263) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1263 : oddCount 1263 13 = 11 ∧ acceleratedOrbit 13 1263 = 27337 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1263 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1263) = 3 ^ 11 * m + 27337 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1263.1, data_13_1263.2]

end Collatz.Research.StoppingAtlas.Batch0549
