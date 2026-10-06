import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0149

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1249. -/
theorem bounds_11_1249 : exactInterval 11 1249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1249 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1249) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1249 : oddCount 1249 11 = 8 ∧ acceleratedOrbit 11 1249 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1249 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1249) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1249.1, data_11_1249.2]

/-- Complete interval computation for depth 11, residue 1250. -/
theorem bounds_11_1250 : exactInterval 11 1250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1250 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1250) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1250 : oddCount 1250 11 = 3 ∧ acceleratedOrbit 11 1250 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1250 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1250) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1250.1, data_11_1250.2]

/-- Complete interval computation for depth 11, residue 1251. -/
theorem bounds_11_1251 : exactInterval 11 1251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1251 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1251) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1251 : oddCount 1251 11 = 3 ∧ acceleratedOrbit 11 1251 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1251 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1251) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1251.1, data_11_1251.2]

/-- Complete interval computation for depth 11, residue 1252. -/
theorem bounds_11_1252 : exactInterval 11 1252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1252 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1252) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1252 : oddCount 1252 11 = 6 ∧ acceleratedOrbit 11 1252 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1252 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1252) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1252.1, data_11_1252.2]

/-- Complete interval computation for depth 11, residue 1253. -/
theorem bounds_11_1253 : exactInterval 11 1253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1253 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1253) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1253 : oddCount 1253 11 = 6 ∧ acceleratedOrbit 11 1253 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1253 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1253) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1253.1, data_11_1253.2]

/-- Complete interval computation for depth 11, residue 1254. -/
theorem bounds_11_1254 : exactInterval 11 1254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1254 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1254) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1254 : oddCount 1254 11 = 6 ∧ acceleratedOrbit 11 1254 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1254 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1254) = 3 ^ 6 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1254.1, data_11_1254.2]

/-- Complete interval computation for depth 11, residue 1255. -/
theorem bounds_11_1255 : exactInterval 11 1255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1255 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1255) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1255 : oddCount 1255 11 = 8 ∧ acceleratedOrbit 11 1255 = 4025 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1255 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1255) = 3 ^ 8 * m + 4025 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1255.1, data_11_1255.2]

/-- Complete interval computation for depth 11, residue 1256. -/
theorem bounds_11_1256 : exactInterval 11 1256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1256 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1256) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1256 : oddCount 1256 11 = 5 ∧ acceleratedOrbit 11 1256 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1256 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1256) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1256.1, data_11_1256.2]

/-- Complete interval computation for depth 11, residue 1257. -/
theorem bounds_11_1257 : exactInterval 11 1257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1257 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1257) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1257 : oddCount 1257 11 = 6 ∧ acceleratedOrbit 11 1257 = 448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1257 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1257) = 3 ^ 6 * m + 448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1257.1, data_11_1257.2]

/-- Complete interval computation for depth 11, residue 1258. -/
theorem bounds_11_1258 : exactInterval 11 1258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1258 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1258) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1258 : oddCount 1258 11 = 5 ∧ acceleratedOrbit 11 1258 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1258 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1258) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1258.1, data_11_1258.2]

/-- Complete interval computation for depth 11, residue 1259. -/
theorem bounds_11_1259 : exactInterval 11 1259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1259 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1259) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1259 : oddCount 1259 11 = 8 ∧ acceleratedOrbit 11 1259 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1259 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1259) = 3 ^ 8 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1259.1, data_11_1259.2]

/-- Complete interval computation for depth 11, residue 1260. -/
theorem bounds_11_1260 : exactInterval 11 1260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1260 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1260) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1260 : oddCount 1260 11 = 4 ∧ acceleratedOrbit 11 1260 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1260 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1260) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1260.1, data_11_1260.2]

/-- Complete interval computation for depth 11, residue 1261. -/
theorem bounds_11_1261 : exactInterval 11 1261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1261 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1261) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1261 : oddCount 1261 11 = 4 ∧ acceleratedOrbit 11 1261 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1261 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1261) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1261.1, data_11_1261.2]

/-- Complete interval computation for depth 11, residue 1262. -/
theorem bounds_11_1262 : exactInterval 11 1262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1262 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1262) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1262 : oddCount 1262 11 = 4 ∧ acceleratedOrbit 11 1262 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1262 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1262) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1262.1, data_11_1262.2]

/-- Complete interval computation for depth 11, residue 1263. -/
theorem bounds_11_1263 : exactInterval 11 1263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1263 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1263) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1263 : oddCount 1263 11 = 10 ∧ acceleratedOrbit 11 1263 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1263 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1263) = 3 ^ 10 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1263.1, data_11_1263.2]

end Collatz.Research.StoppingAtlas.Batch0149
