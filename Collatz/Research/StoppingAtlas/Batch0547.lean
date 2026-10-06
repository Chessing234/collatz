import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0547

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1218. -/
theorem bounds_13_1218 : exactInterval 13 1218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1218 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1218) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1218 : oddCount 1218 13 = 6 ∧ acceleratedOrbit 13 1218 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1218 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1218) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1218.1, data_13_1218.2]

/-- Complete interval computation for depth 13, residue 1219. -/
theorem bounds_13_1219 : exactInterval 13 1219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1219 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1219) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1219 : oddCount 1219 13 = 6 ∧ acceleratedOrbit 13 1219 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1219 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1219) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1219.1, data_13_1219.2]

/-- Complete interval computation for depth 13, residue 1220. -/
theorem bounds_13_1220 : exactInterval 13 1220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1220 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1220) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1220 : oddCount 1220 13 = 5 ∧ acceleratedOrbit 13 1220 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1220 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1220) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1220.1, data_13_1220.2]

/-- Complete interval computation for depth 13, residue 1221. -/
theorem bounds_13_1221 : exactInterval 13 1221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1221 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1221) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1221 : oddCount 1221 13 = 5 ∧ acceleratedOrbit 13 1221 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1221 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1221) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1221.1, data_13_1221.2]

/-- Complete interval computation for depth 13, residue 1222. -/
theorem bounds_13_1222 : exactInterval 13 1222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1222 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1222) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1222 : oddCount 1222 13 = 5 ∧ acceleratedOrbit 13 1222 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1222 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1222) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1222.1, data_13_1222.2]

/-- Complete interval computation for depth 13, residue 1223. -/
theorem bounds_13_1223 : exactInterval 13 1223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1223 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1223) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1223 : oddCount 1223 13 = 6 ∧ acceleratedOrbit 13 1223 = 109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1223 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1223) = 3 ^ 6 * m + 109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1223.1, data_13_1223.2]

/-- Complete interval computation for depth 13, residue 1224. -/
theorem bounds_13_1224 : exactInterval 13 1224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1224 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1224) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1224 : oddCount 1224 13 = 5 ∧ acceleratedOrbit 13 1224 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1224 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1224) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1224.1, data_13_1224.2]

/-- Complete interval computation for depth 13, residue 1225. -/
theorem bounds_13_1225 : exactInterval 13 1225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1225 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1225) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1225 : oddCount 1225 13 = 6 ∧ acceleratedOrbit 13 1225 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1225 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1225) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1225.1, data_13_1225.2]

/-- Complete interval computation for depth 13, residue 1226. -/
theorem bounds_13_1226 : exactInterval 13 1226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1226 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1226) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1226 : oddCount 1226 13 = 5 ∧ acceleratedOrbit 13 1226 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1226 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1226) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1226.1, data_13_1226.2]

/-- Complete interval computation for depth 13, residue 1227. -/
theorem bounds_13_1227 : exactInterval 13 1227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1227 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1227) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1227 : oddCount 1227 13 = 6 ∧ acceleratedOrbit 13 1227 = 110 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1227 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1227) = 3 ^ 6 * m + 110 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1227.1, data_13_1227.2]

/-- Complete interval computation for depth 13, residue 1228. -/
theorem bounds_13_1228 : exactInterval 13 1228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1228 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1228) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1228 : oddCount 1228 13 = 5 ∧ acceleratedOrbit 13 1228 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1228 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1228) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1228.1, data_13_1228.2]

/-- Complete interval computation for depth 13, residue 1229. -/
theorem bounds_13_1229 : exactInterval 13 1229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1229 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1229) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1229 : oddCount 1229 13 = 5 ∧ acceleratedOrbit 13 1229 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1229 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1229) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1229.1, data_13_1229.2]

/-- Complete interval computation for depth 13, residue 1230. -/
theorem bounds_13_1230 : exactInterval 13 1230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1230 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1230) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1230 : oddCount 1230 13 = 7 ∧ acceleratedOrbit 13 1230 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1230 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1230) = 3 ^ 7 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1230.1, data_13_1230.2]

/-- Complete interval computation for depth 13, residue 1231. -/
theorem bounds_13_1231 : exactInterval 13 1231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1231 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1231) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1231 : oddCount 1231 13 = 7 ∧ acceleratedOrbit 13 1231 = 329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1231 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1231) = 3 ^ 7 * m + 329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1231.1, data_13_1231.2]

/-- Complete interval computation for depth 13, residue 1232. -/
theorem bounds_13_1232 : exactInterval 13 1232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1232 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1232) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1232 : oddCount 1232 13 = 4 ∧ acceleratedOrbit 13 1232 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1232 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1232) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1232.1, data_13_1232.2]

end Collatz.Research.StoppingAtlas.Batch0547
