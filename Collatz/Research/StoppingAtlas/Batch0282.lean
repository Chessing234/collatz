import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0282

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1244. -/
theorem bounds_12_1244 : exactInterval 12 1244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1244 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1244) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1244 : oddCount 1244 12 = 7 ∧ acceleratedOrbit 12 1244 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1244 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1244) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1244.1, data_12_1244.2]

/-- Complete interval computation for depth 12, residue 1245. -/
theorem bounds_12_1245 : exactInterval 12 1245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1245 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1245) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1245 : oddCount 1245 12 = 7 ∧ acceleratedOrbit 12 1245 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1245 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1245) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1245.1, data_12_1245.2]

/-- Complete interval computation for depth 12, residue 1246. -/
theorem bounds_12_1246 : exactInterval 12 1246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1246 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1246) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1246 : oddCount 1246 12 = 8 ∧ acceleratedOrbit 12 1246 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1246 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1246) = 3 ^ 8 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1246.1, data_12_1246.2]

/-- Complete interval computation for depth 12, residue 1247. -/
theorem bounds_12_1247 : exactInterval 12 1247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1247 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1247) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1247 : oddCount 1247 12 = 8 ∧ acceleratedOrbit 12 1247 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1247 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1247) = 3 ^ 8 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1247.1, data_12_1247.2]

/-- Complete interval computation for depth 12, residue 1248. -/
theorem bounds_12_1248 : exactInterval 12 1248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1248 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1248) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1248 : oddCount 1248 12 = 5 ∧ acceleratedOrbit 12 1248 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1248 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1248) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1248.1, data_12_1248.2]

/-- Complete interval computation for depth 12, residue 1249. -/
theorem bounds_12_1249 : exactInterval 12 1249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1249 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1249) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1249 : oddCount 1249 12 = 9 ∧ acceleratedOrbit 12 1249 = 6014 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1249 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1249) = 3 ^ 9 * m + 6014 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1249.1, data_12_1249.2]

/-- Complete interval computation for depth 12, residue 1250. -/
theorem bounds_12_1250 : exactInterval 12 1250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1250 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1250) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1250 : oddCount 1250 12 = 4 ∧ acceleratedOrbit 12 1250 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1250 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1250) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1250.1, data_12_1250.2]

/-- Complete interval computation for depth 12, residue 1251. -/
theorem bounds_12_1251 : exactInterval 12 1251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1251 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1251) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1251 : oddCount 1251 12 = 4 ∧ acceleratedOrbit 12 1251 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1251 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1251) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1251.1, data_12_1251.2]

/-- Complete interval computation for depth 12, residue 1252. -/
theorem bounds_12_1252 : exactInterval 12 1252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1252 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1252) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1252 : oddCount 1252 12 = 7 ∧ acceleratedOrbit 12 1252 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1252 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1252) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1252.1, data_12_1252.2]

/-- Complete interval computation for depth 12, residue 1253. -/
theorem bounds_12_1253 : exactInterval 12 1253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1253 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1253) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1253 : oddCount 1253 12 = 7 ∧ acceleratedOrbit 12 1253 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1253 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1253) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1253.1, data_12_1253.2]

/-- Complete interval computation for depth 12, residue 1254. -/
theorem bounds_12_1254 : exactInterval 12 1254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1254 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1254) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1254 : oddCount 1254 12 = 7 ∧ acceleratedOrbit 12 1254 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1254 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1254) = 3 ^ 7 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1254.1, data_12_1254.2]

/-- Complete interval computation for depth 12, residue 1255. -/
theorem bounds_12_1255 : exactInterval 12 1255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1255 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1255) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1255 : oddCount 1255 12 = 9 ∧ acceleratedOrbit 12 1255 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1255 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1255) = 3 ^ 9 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1255.1, data_12_1255.2]

/-- Complete interval computation for depth 12, residue 1256. -/
theorem bounds_12_1256 : exactInterval 12 1256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1256 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1256) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1256 : oddCount 1256 12 = 5 ∧ acceleratedOrbit 12 1256 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1256 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1256) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1256.1, data_12_1256.2]

/-- Complete interval computation for depth 12, residue 1257. -/
theorem bounds_12_1257 : exactInterval 12 1257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1257 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1257) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1257 : oddCount 1257 12 = 6 ∧ acceleratedOrbit 12 1257 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1257 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1257) = 3 ^ 6 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1257.1, data_12_1257.2]

/-- Complete interval computation for depth 12, residue 1258. -/
theorem bounds_12_1258 : exactInterval 12 1258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1258 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1258) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1258 : oddCount 1258 12 = 5 ∧ acceleratedOrbit 12 1258 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1258 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1258) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1258.1, data_12_1258.2]

end Collatz.Research.StoppingAtlas.Batch0282
