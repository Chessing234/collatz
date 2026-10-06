import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0281

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1228. -/
theorem bounds_12_1228 : exactInterval 12 1228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1228 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1228) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1228 : oddCount 1228 12 = 5 ∧ acceleratedOrbit 12 1228 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1228 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1228) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1228.1, data_12_1228.2]

/-- Complete interval computation for depth 12, residue 1229. -/
theorem bounds_12_1229 : exactInterval 12 1229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1229 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1229) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1229 : oddCount 1229 12 = 5 ∧ acceleratedOrbit 12 1229 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1229 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1229) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1229.1, data_12_1229.2]

/-- Complete interval computation for depth 12, residue 1230. -/
theorem bounds_12_1230 : exactInterval 12 1230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1230 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1230) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1230 : oddCount 1230 12 = 7 ∧ acceleratedOrbit 12 1230 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1230 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1230) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1230.1, data_12_1230.2]

/-- Complete interval computation for depth 12, residue 1231. -/
theorem bounds_12_1231 : exactInterval 12 1231 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1231 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1231) 12 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1231 : oddCount 1231 12 = 7 ∧ acceleratedOrbit 12 1231 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1231 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1231) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1231.1, data_12_1231.2]

/-- Complete interval computation for depth 12, residue 1232. -/
theorem bounds_12_1232 : exactInterval 12 1232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1232 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1232) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1232 : oddCount 1232 12 = 4 ∧ acceleratedOrbit 12 1232 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1232 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1232) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1232.1, data_12_1232.2]

/-- Complete interval computation for depth 12, residue 1233. -/
theorem bounds_12_1233 : exactInterval 12 1233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1233 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1233) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1233 : oddCount 1233 12 = 7 ∧ acceleratedOrbit 12 1233 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1233 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1233) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1233.1, data_12_1233.2]

/-- Complete interval computation for depth 12, residue 1234. -/
theorem bounds_12_1234 : exactInterval 12 1234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1234 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1234) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1234 : oddCount 1234 12 = 7 ∧ acceleratedOrbit 12 1234 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1234 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1234) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1234.1, data_12_1234.2]

/-- Complete interval computation for depth 12, residue 1235. -/
theorem bounds_12_1235 : exactInterval 12 1235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1235 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1235) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1235 : oddCount 1235 12 = 7 ∧ acceleratedOrbit 12 1235 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1235 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1235) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1235.1, data_12_1235.2]

/-- Complete interval computation for depth 12, residue 1236. -/
theorem bounds_12_1236 : exactInterval 12 1236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1236 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1236) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1236 : oddCount 1236 12 = 4 ∧ acceleratedOrbit 12 1236 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1236 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1236) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1236.1, data_12_1236.2]

/-- Complete interval computation for depth 12, residue 1237. -/
theorem bounds_12_1237 : exactInterval 12 1237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1237 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1237) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1237 : oddCount 1237 12 = 4 ∧ acceleratedOrbit 12 1237 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1237 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1237) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1237.1, data_12_1237.2]

/-- Complete interval computation for depth 12, residue 1238. -/
theorem bounds_12_1238 : exactInterval 12 1238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1238 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1238) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1238 : oddCount 1238 12 = 6 ∧ acceleratedOrbit 12 1238 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1238 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1238) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1238.1, data_12_1238.2]

/-- Complete interval computation for depth 12, residue 1239. -/
theorem bounds_12_1239 : exactInterval 12 1239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1239 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1239) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1239 : oddCount 1239 12 = 6 ∧ acceleratedOrbit 12 1239 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1239 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1239) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1239.1, data_12_1239.2]

/-- Complete interval computation for depth 12, residue 1240. -/
theorem bounds_12_1240 : exactInterval 12 1240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1240 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1240) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1240 : oddCount 1240 12 = 7 ∧ acceleratedOrbit 12 1240 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1240 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1240) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1240.1, data_12_1240.2]

/-- Complete interval computation for depth 12, residue 1241. -/
theorem bounds_12_1241 : exactInterval 12 1241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1241 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1241) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1241 : oddCount 1241 12 = 5 ∧ acceleratedOrbit 12 1241 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1241 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1241) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1241.1, data_12_1241.2]

/-- Complete interval computation for depth 12, residue 1242. -/
theorem bounds_12_1242 : exactInterval 12 1242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1242 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1242) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1242 : oddCount 1242 12 = 7 ∧ acceleratedOrbit 12 1242 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1242 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1242) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1242.1, data_12_1242.2]

/-- Complete interval computation for depth 12, residue 1243. -/
theorem bounds_12_1243 : exactInterval 12 1243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1243 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1243) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1243 : oddCount 1243 12 = 7 ∧ acceleratedOrbit 12 1243 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1243 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1243) = 3 ^ 7 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1243.1, data_12_1243.2]

end Collatz.Research.StoppingAtlas.Batch0281
