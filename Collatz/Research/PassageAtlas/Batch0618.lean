import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0618

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20217. -/
theorem bounds_15_20217 : exactInterval 15 20217 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20217 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20217) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20217 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20217 : oddCount 20217 15 = 9 ∧ acceleratedOrbit 15 20217 = 12149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20217 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20217) = 3 ^ 9 * m + 12149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20217.1, data_15_20217.2]

/-- Complete interval computation for depth 15, residue 20218. -/
theorem bounds_15_20218 : exactInterval 15 20218 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20218 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20218) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20218 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20218 : oddCount 20218 15 = 10 ∧ acceleratedOrbit 15 20218 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20218 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20218) = 3 ^ 10 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20218.1, data_15_20218.2]

/-- Complete interval computation for depth 15, residue 20219. -/
theorem bounds_15_20219 : exactInterval 15 20219 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20219 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20219) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20219 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20219 : oddCount 20219 15 = 10 ∧ acceleratedOrbit 15 20219 = 36440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20219 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20219) = 3 ^ 10 * m + 36440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20219.1, data_15_20219.2]

/-- Complete interval computation for depth 15, residue 20220. -/
theorem bounds_15_20220 : exactInterval 15 20220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20220 : oddCount 20220 15 = 10 ∧ acceleratedOrbit 15 20220 = 36445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20220) = 3 ^ 10 * m + 36445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20220.1, data_15_20220.2]

/-- Complete interval computation for depth 15, residue 20221. -/
theorem bounds_15_20221 : exactInterval 15 20221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20221 : oddCount 20221 15 = 10 ∧ acceleratedOrbit 15 20221 = 36445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20221) = 3 ^ 10 * m + 36445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20221.1, data_15_20221.2]

/-- Complete interval computation for depth 15, residue 20222. -/
theorem bounds_15_20222 : exactInterval 15 20222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20222 : oddCount 20222 15 = 10 ∧ acceleratedOrbit 15 20222 = 36445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20222) = 3 ^ 10 * m + 36445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20222.1, data_15_20222.2]

/-- Complete interval computation for depth 15, residue 20223. -/
theorem bounds_15_20223 : exactInterval 15 20223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20223 : oddCount 20223 15 = 11 ∧ acceleratedOrbit 15 20223 = 109333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20223) = 3 ^ 11 * m + 109333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20223.1, data_15_20223.2]

/-- Complete interval computation for depth 15, residue 20224. -/
theorem bounds_15_20224 : exactInterval 15 20224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20224 : oddCount 20224 15 = 5 ∧ acceleratedOrbit 15 20224 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20224) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20224.1, data_15_20224.2]

/-- Complete interval computation for depth 15, residue 20225. -/
theorem bounds_15_20225 : exactInterval 15 20225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20225 : oddCount 20225 15 = 4 ∧ acceleratedOrbit 15 20225 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20225) = 3 ^ 4 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20225.1, data_15_20225.2]

/-- Complete interval computation for depth 15, residue 20226. -/
theorem bounds_15_20226 : exactInterval 15 20226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20226 : oddCount 20226 15 = 8 ∧ acceleratedOrbit 15 20226 = 4052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20226) = 3 ^ 8 * m + 4052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20226.1, data_15_20226.2]

/-- Complete interval computation for depth 15, residue 20227. -/
theorem bounds_15_20227 : exactInterval 15 20227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20227 : oddCount 20227 15 = 8 ∧ acceleratedOrbit 15 20227 = 4052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20227) = 3 ^ 8 * m + 4052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20227.1, data_15_20227.2]

/-- Complete interval computation for depth 15, residue 20228. -/
theorem bounds_15_20228 : exactInterval 15 20228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20228 : oddCount 20228 15 = 7 ∧ acceleratedOrbit 15 20228 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20228) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20228.1, data_15_20228.2]

/-- Complete interval computation for depth 15, residue 20229. -/
theorem bounds_15_20229 : exactInterval 15 20229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20229 : oddCount 20229 15 = 7 ∧ acceleratedOrbit 15 20229 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20229) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20229.1, data_15_20229.2]

/-- Complete interval computation for depth 15, residue 20230. -/
theorem bounds_15_20230 : exactInterval 15 20230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20230 : oddCount 20230 15 = 7 ∧ acceleratedOrbit 15 20230 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20230) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20230.1, data_15_20230.2]

/-- Complete interval computation for depth 15, residue 20231. -/
theorem bounds_15_20231 : exactInterval 15 20231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20231 : oddCount 20231 15 = 8 ∧ acceleratedOrbit 15 20231 = 4052 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20231) = 3 ^ 8 * m + 4052 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20231.1, data_15_20231.2]

/-- Complete interval computation for depth 15, residue 20232. -/
theorem bounds_15_20232 : exactInterval 15 20232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20232 : oddCount 20232 15 = 7 ∧ acceleratedOrbit 15 20232 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20232) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20232.1, data_15_20232.2]

/-- Complete interval computation for depth 15, residue 20233. -/
theorem bounds_15_20233 : exactInterval 15 20233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20233 : oddCount 20233 15 = 9 ∧ acceleratedOrbit 15 20233 = 12155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20233) = 3 ^ 9 * m + 12155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20233.1, data_15_20233.2]

/-- Complete interval computation for depth 15, residue 20234. -/
theorem bounds_15_20234 : exactInterval 15 20234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20234 : oddCount 20234 15 = 7 ∧ acceleratedOrbit 15 20234 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20234) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20234.1, data_15_20234.2]

/-- Complete interval computation for depth 15, residue 20235. -/
theorem bounds_15_20235 : exactInterval 15 20235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20235 : oddCount 20235 15 = 7 ∧ acceleratedOrbit 15 20235 = 1351 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20235) = 3 ^ 7 * m + 1351 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20235.1, data_15_20235.2]

/-- Complete interval computation for depth 15, residue 20236. -/
theorem bounds_15_20236 : exactInterval 15 20236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20236 : oddCount 20236 15 = 7 ∧ acceleratedOrbit 15 20236 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20236) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20236.1, data_15_20236.2]

/-- Complete interval computation for depth 15, residue 20237. -/
theorem bounds_15_20237 : exactInterval 15 20237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20237 : oddCount 20237 15 = 7 ∧ acceleratedOrbit 15 20237 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20237) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20237.1, data_15_20237.2]

/-- Complete interval computation for depth 15, residue 20238. -/
theorem bounds_15_20238 : exactInterval 15 20238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20238 : oddCount 20238 15 = 7 ∧ acceleratedOrbit 15 20238 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20238) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20238.1, data_15_20238.2]

/-- Complete interval computation for depth 15, residue 20239. -/
theorem bounds_15_20239 : exactInterval 15 20239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20239 : oddCount 20239 15 = 7 ∧ acceleratedOrbit 15 20239 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20239) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20239.1, data_15_20239.2]

/-- Complete interval computation for depth 15, residue 20240. -/
theorem bounds_15_20240 : exactInterval 15 20240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20240 : oddCount 20240 15 = 5 ∧ acceleratedOrbit 15 20240 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20240) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20240.1, data_15_20240.2]

/-- Complete interval computation for depth 15, residue 20241. -/
theorem bounds_15_20241 : exactInterval 15 20241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20241 : oddCount 20241 15 = 7 ∧ acceleratedOrbit 15 20241 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20241) = 3 ^ 7 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20241.1, data_15_20241.2]

/-- Complete interval computation for depth 15, residue 20242. -/
theorem bounds_15_20242 : exactInterval 15 20242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20242 : oddCount 20242 15 = 8 ∧ acceleratedOrbit 15 20242 = 4054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20242) = 3 ^ 8 * m + 4054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20242.1, data_15_20242.2]

/-- Complete interval computation for depth 15, residue 20243. -/
theorem bounds_15_20243 : exactInterval 15 20243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20243 : oddCount 20243 15 = 8 ∧ acceleratedOrbit 15 20243 = 4054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20243) = 3 ^ 8 * m + 4054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20243.1, data_15_20243.2]

/-- Complete interval computation for depth 15, residue 20244. -/
theorem bounds_15_20244 : exactInterval 15 20244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20244 : oddCount 20244 15 = 5 ∧ acceleratedOrbit 15 20244 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20244) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20244.1, data_15_20244.2]

/-- Complete interval computation for depth 15, residue 20245. -/
theorem bounds_15_20245 : exactInterval 15 20245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20245 : oddCount 20245 15 = 5 ∧ acceleratedOrbit 15 20245 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20245) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20245.1, data_15_20245.2]

/-- Complete interval computation for depth 15, residue 20246. -/
theorem bounds_15_20246 : exactInterval 15 20246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20246 : oddCount 20246 15 = 8 ∧ acceleratedOrbit 15 20246 = 4055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20246) = 3 ^ 8 * m + 4055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20246.1, data_15_20246.2]

/-- Complete interval computation for depth 15, residue 20247. -/
theorem bounds_15_20247 : exactInterval 15 20247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20247 : oddCount 20247 15 = 8 ∧ acceleratedOrbit 15 20247 = 4055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20247) = 3 ^ 8 * m + 4055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20247.1, data_15_20247.2]

/-- Complete interval computation for depth 15, residue 20248. -/
theorem bounds_15_20248 : exactInterval 15 20248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20248 : oddCount 20248 15 = 5 ∧ acceleratedOrbit 15 20248 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20248) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20248.1, data_15_20248.2]

/-- Complete interval computation for depth 15, residue 20249. -/
theorem bounds_15_20249 : exactInterval 15 20249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20249 : oddCount 20249 15 = 8 ∧ acceleratedOrbit 15 20249 = 4055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20249) = 3 ^ 8 * m + 4055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20249.1, data_15_20249.2]

end Collatz.Research.PassageAtlas.Batch0618
