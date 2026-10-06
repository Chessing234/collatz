import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0280

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1213. -/
theorem bounds_12_1213 : exactInterval 12 1213 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1213 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1213) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1213 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1213 : oddCount 1213 12 = 7 ∧ acceleratedOrbit 12 1213 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1213 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1213) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1213.1, data_12_1213.2]

/-- Complete interval computation for depth 12, residue 1214. -/
theorem bounds_12_1214 : exactInterval 12 1214 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1214 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1214) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1214 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1214 : oddCount 1214 12 = 7 ∧ acceleratedOrbit 12 1214 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1214 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1214) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1214.1, data_12_1214.2]

/-- Complete interval computation for depth 12, residue 1215. -/
theorem bounds_12_1215 : exactInterval 12 1215 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1215 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1215) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1215 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1215 : oddCount 1215 12 = 8 ∧ acceleratedOrbit 12 1215 = 1948 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1215 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1215) = 3 ^ 8 * m + 1948 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1215.1, data_12_1215.2]

/-- Complete interval computation for depth 12, residue 1216. -/
theorem bounds_12_1216 : exactInterval 12 1216 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1216 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1216) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1216 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1216 : oddCount 1216 12 = 4 ∧ acceleratedOrbit 12 1216 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1216 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1216) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1216.1, data_12_1216.2]

/-- Complete interval computation for depth 12, residue 1217. -/
theorem bounds_12_1217 : exactInterval 12 1217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1217 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1217) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1217 : oddCount 1217 12 = 6 ∧ acceleratedOrbit 12 1217 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1217 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1217) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1217.1, data_12_1217.2]

/-- Complete interval computation for depth 12, residue 1218. -/
theorem bounds_12_1218 : exactInterval 12 1218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1218 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1218) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1218 : oddCount 1218 12 = 6 ∧ acceleratedOrbit 12 1218 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1218 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1218) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1218.1, data_12_1218.2]

/-- Complete interval computation for depth 12, residue 1219. -/
theorem bounds_12_1219 : exactInterval 12 1219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1219 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1219) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1219 : oddCount 1219 12 = 6 ∧ acceleratedOrbit 12 1219 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1219 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1219) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1219.1, data_12_1219.2]

/-- Complete interval computation for depth 12, residue 1220. -/
theorem bounds_12_1220 : exactInterval 12 1220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1220 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1220) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1220 : oddCount 1220 12 = 5 ∧ acceleratedOrbit 12 1220 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1220 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1220) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1220.1, data_12_1220.2]

/-- Complete interval computation for depth 12, residue 1221. -/
theorem bounds_12_1221 : exactInterval 12 1221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1221 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1221) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1221 : oddCount 1221 12 = 5 ∧ acceleratedOrbit 12 1221 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1221 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1221) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1221.1, data_12_1221.2]

/-- Complete interval computation for depth 12, residue 1222. -/
theorem bounds_12_1222 : exactInterval 12 1222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1222 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1222) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1222 : oddCount 1222 12 = 5 ∧ acceleratedOrbit 12 1222 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1222 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1222) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1222.1, data_12_1222.2]

/-- Complete interval computation for depth 12, residue 1223. -/
theorem bounds_12_1223 : exactInterval 12 1223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1223 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1223) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1223 : oddCount 1223 12 = 6 ∧ acceleratedOrbit 12 1223 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1223 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1223) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1223.1, data_12_1223.2]

/-- Complete interval computation for depth 12, residue 1224. -/
theorem bounds_12_1224 : exactInterval 12 1224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1224 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1224) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1224 : oddCount 1224 12 = 5 ∧ acceleratedOrbit 12 1224 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1224 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1224) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1224.1, data_12_1224.2]

/-- Complete interval computation for depth 12, residue 1225. -/
theorem bounds_12_1225 : exactInterval 12 1225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1225 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1225) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1225 : oddCount 1225 12 = 5 ∧ acceleratedOrbit 12 1225 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1225 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1225) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1225.1, data_12_1225.2]

/-- Complete interval computation for depth 12, residue 1226. -/
theorem bounds_12_1226 : exactInterval 12 1226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1226 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1226) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1226 : oddCount 1226 12 = 5 ∧ acceleratedOrbit 12 1226 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1226 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1226) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1226.1, data_12_1226.2]

/-- Complete interval computation for depth 12, residue 1227. -/
theorem bounds_12_1227 : exactInterval 12 1227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1227 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1227) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1227 : oddCount 1227 12 = 5 ∧ acceleratedOrbit 12 1227 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1227 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1227) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1227.1, data_12_1227.2]

end Collatz.Research.StoppingAtlas.Batch0280
