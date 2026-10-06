import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0147

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1218. -/
theorem bounds_11_1218 : exactInterval 11 1218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1218 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1218) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1218 : oddCount 1218 11 = 5 ∧ acceleratedOrbit 11 1218 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1218 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1218) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1218.1, data_11_1218.2]

/-- Complete interval computation for depth 11, residue 1219. -/
theorem bounds_11_1219 : exactInterval 11 1219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1219 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1219) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1219 : oddCount 1219 11 = 5 ∧ acceleratedOrbit 11 1219 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1219 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1219) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1219.1, data_11_1219.2]

/-- Complete interval computation for depth 11, residue 1220. -/
theorem bounds_11_1220 : exactInterval 11 1220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1220 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1220) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1220 : oddCount 1220 11 = 4 ∧ acceleratedOrbit 11 1220 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1220 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1220) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1220.1, data_11_1220.2]

/-- Complete interval computation for depth 11, residue 1221. -/
theorem bounds_11_1221 : exactInterval 11 1221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1221 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1221) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1221 : oddCount 1221 11 = 4 ∧ acceleratedOrbit 11 1221 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1221 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1221) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1221.1, data_11_1221.2]

/-- Complete interval computation for depth 11, residue 1222. -/
theorem bounds_11_1222 : exactInterval 11 1222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1222 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1222) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1222 : oddCount 1222 11 = 4 ∧ acceleratedOrbit 11 1222 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1222 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1222) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1222.1, data_11_1222.2]

/-- Complete interval computation for depth 11, residue 1223. -/
theorem bounds_11_1223 : exactInterval 11 1223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1223 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1223) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1223 : oddCount 1223 11 = 6 ∧ acceleratedOrbit 11 1223 = 436 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1223 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1223) = 3 ^ 6 * m + 436 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1223.1, data_11_1223.2]

/-- Complete interval computation for depth 11, residue 1224. -/
theorem bounds_11_1224 : exactInterval 11 1224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1224 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1224) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1224 : oddCount 1224 11 = 4 ∧ acceleratedOrbit 11 1224 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1224 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1224) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1224.1, data_11_1224.2]

/-- Complete interval computation for depth 11, residue 1225. -/
theorem bounds_11_1225 : exactInterval 11 1225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1225 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1225) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1225 : oddCount 1225 11 = 5 ∧ acceleratedOrbit 11 1225 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1225 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1225) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1225.1, data_11_1225.2]

/-- Complete interval computation for depth 11, residue 1226. -/
theorem bounds_11_1226 : exactInterval 11 1226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1226 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1226) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1226 : oddCount 1226 11 = 4 ∧ acceleratedOrbit 11 1226 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1226 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1226) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1226.1, data_11_1226.2]

/-- Complete interval computation for depth 11, residue 1227. -/
theorem bounds_11_1227 : exactInterval 11 1227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1227 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1227) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1227 : oddCount 1227 11 = 5 ∧ acceleratedOrbit 11 1227 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1227 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1227) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1227.1, data_11_1227.2]

/-- Complete interval computation for depth 11, residue 1228. -/
theorem bounds_11_1228 : exactInterval 11 1228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1228 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1228) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1228 : oddCount 1228 11 = 4 ∧ acceleratedOrbit 11 1228 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1228 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1228) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1228.1, data_11_1228.2]

/-- Complete interval computation for depth 11, residue 1229. -/
theorem bounds_11_1229 : exactInterval 11 1229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1229 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1229) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1229 : oddCount 1229 11 = 4 ∧ acceleratedOrbit 11 1229 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1229 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1229) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1229.1, data_11_1229.2]

/-- Complete interval computation for depth 11, residue 1230. -/
theorem bounds_11_1230 : exactInterval 11 1230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1230 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1230) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1230 : oddCount 1230 11 = 7 ∧ acceleratedOrbit 11 1230 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1230 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1230) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1230.1, data_11_1230.2]

/-- Complete interval computation for depth 11, residue 1231. -/
theorem bounds_11_1231 : exactInterval 11 1231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1231 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1231) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1231 : oddCount 1231 11 = 7 ∧ acceleratedOrbit 11 1231 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1231 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1231) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1231.1, data_11_1231.2]

/-- Complete interval computation for depth 11, residue 1232. -/
theorem bounds_11_1232 : exactInterval 11 1232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1232 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1232) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1232 : oddCount 1232 11 = 3 ∧ acceleratedOrbit 11 1232 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1232 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1232) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1232.1, data_11_1232.2]

end Collatz.Research.StoppingAtlas.Batch0147
