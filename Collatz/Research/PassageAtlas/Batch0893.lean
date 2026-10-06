import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0893

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29229. -/
theorem bounds_15_29229 : exactInterval 15 29229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29229 : oddCount 29229 15 = 7 ∧ acceleratedOrbit 15 29229 = 1952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29229) = 3 ^ 7 * m + 1952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29229.1, data_15_29229.2]

/-- Complete interval computation for depth 15, residue 29230. -/
theorem bounds_15_29230 : exactInterval 15 29230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29230 : oddCount 29230 15 = 7 ∧ acceleratedOrbit 15 29230 = 1952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29230) = 3 ^ 7 * m + 1952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29230.1, data_15_29230.2]

/-- Complete interval computation for depth 15, residue 29231. -/
theorem bounds_15_29231 : exactInterval 15 29231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29231 : oddCount 29231 15 = 10 ∧ acceleratedOrbit 15 29231 = 52678 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29231) = 3 ^ 10 * m + 52678 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29231.1, data_15_29231.2]

/-- Complete interval computation for depth 15, residue 29232. -/
theorem bounds_15_29232 : exactInterval 15 29232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29232 : oddCount 29232 15 = 5 ∧ acceleratedOrbit 15 29232 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29232) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29232.1, data_15_29232.2]

/-- Complete interval computation for depth 15, residue 29233. -/
theorem bounds_15_29233 : exactInterval 15 29233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29233 : oddCount 29233 15 = 7 ∧ acceleratedOrbit 15 29233 = 1952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29233) = 3 ^ 7 * m + 1952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29233.1, data_15_29233.2]

/-- Complete interval computation for depth 15, residue 29234. -/
theorem bounds_15_29234 : exactInterval 15 29234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29234 : oddCount 29234 15 = 7 ∧ acceleratedOrbit 15 29234 = 1952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29234) = 3 ^ 7 * m + 1952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29234.1, data_15_29234.2]

/-- Complete interval computation for depth 15, residue 29235. -/
theorem bounds_15_29235 : exactInterval 15 29235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29235 : oddCount 29235 15 = 7 ∧ acceleratedOrbit 15 29235 = 1952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29235) = 3 ^ 7 * m + 1952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29235.1, data_15_29235.2]

/-- Complete interval computation for depth 15, residue 29236. -/
theorem bounds_15_29236 : exactInterval 15 29236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29236 : oddCount 29236 15 = 5 ∧ acceleratedOrbit 15 29236 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29236) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29236.1, data_15_29236.2]

/-- Complete interval computation for depth 15, residue 29237. -/
theorem bounds_15_29237 : exactInterval 15 29237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29237 : oddCount 29237 15 = 5 ∧ acceleratedOrbit 15 29237 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29237) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29237.1, data_15_29237.2]

/-- Complete interval computation for depth 15, residue 29238. -/
theorem bounds_15_29238 : exactInterval 15 29238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29238 : oddCount 29238 15 = 10 ∧ acceleratedOrbit 15 29238 = 52694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29238) = 3 ^ 10 * m + 52694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29238.1, data_15_29238.2]

/-- Complete interval computation for depth 15, residue 29239. -/
theorem bounds_15_29239 : exactInterval 15 29239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29239 : oddCount 29239 15 = 10 ∧ acceleratedOrbit 15 29239 = 52694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29239) = 3 ^ 10 * m + 52694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29239.1, data_15_29239.2]

/-- Complete interval computation for depth 15, residue 29240. -/
theorem bounds_15_29240 : exactInterval 15 29240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29240 : oddCount 29240 15 = 8 ∧ acceleratedOrbit 15 29240 = 5858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29240) = 3 ^ 8 * m + 5858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29240.1, data_15_29240.2]

/-- Complete interval computation for depth 15, residue 29241. -/
theorem bounds_15_29241 : exactInterval 15 29241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29241 : oddCount 29241 15 = 9 ∧ acceleratedOrbit 15 29241 = 17567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29241) = 3 ^ 9 * m + 17567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29241.1, data_15_29241.2]

/-- Complete interval computation for depth 15, residue 29242. -/
theorem bounds_15_29242 : exactInterval 15 29242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29242 : oddCount 29242 15 = 8 ∧ acceleratedOrbit 15 29242 = 5858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29242) = 3 ^ 8 * m + 5858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29242.1, data_15_29242.2]

/-- Complete interval computation for depth 15, residue 29243. -/
theorem bounds_15_29243 : exactInterval 15 29243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29243 : oddCount 29243 15 = 8 ∧ acceleratedOrbit 15 29243 = 5858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29243) = 3 ^ 8 * m + 5858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29243.1, data_15_29243.2]

/-- Complete interval computation for depth 15, residue 29244. -/
theorem bounds_15_29244 : exactInterval 15 29244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29244 : oddCount 29244 15 = 8 ∧ acceleratedOrbit 15 29244 = 5858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29244) = 3 ^ 8 * m + 5858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29244.1, data_15_29244.2]

/-- Complete interval computation for depth 15, residue 29245. -/
theorem bounds_15_29245 : exactInterval 15 29245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29245 : oddCount 29245 15 = 8 ∧ acceleratedOrbit 15 29245 = 5858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29245) = 3 ^ 8 * m + 5858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29245.1, data_15_29245.2]

/-- Complete interval computation for depth 15, residue 29246. -/
theorem bounds_15_29246 : exactInterval 15 29246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29246 : oddCount 29246 15 = 9 ∧ acceleratedOrbit 15 29246 = 17570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29246) = 3 ^ 9 * m + 17570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29246.1, data_15_29246.2]

/-- Complete interval computation for depth 15, residue 29247. -/
theorem bounds_15_29247 : exactInterval 15 29247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29247 : oddCount 29247 15 = 9 ∧ acceleratedOrbit 15 29247 = 17570 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29247) = 3 ^ 9 * m + 17570 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29247.1, data_15_29247.2]

/-- Complete interval computation for depth 15, residue 29248. -/
theorem bounds_15_29248 : exactInterval 15 29248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29248 : oddCount 29248 15 = 5 ∧ acceleratedOrbit 15 29248 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29248) = 3 ^ 5 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29248.1, data_15_29248.2]

/-- Complete interval computation for depth 15, residue 29249. -/
theorem bounds_15_29249 : exactInterval 15 29249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29249 : oddCount 29249 15 = 5 ∧ acceleratedOrbit 15 29249 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29249) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29249.1, data_15_29249.2]

/-- Complete interval computation for depth 15, residue 29250. -/
theorem bounds_15_29250 : exactInterval 15 29250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29250 : oddCount 29250 15 = 5 ∧ acceleratedOrbit 15 29250 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29250) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29250.1, data_15_29250.2]

/-- Complete interval computation for depth 15, residue 29251. -/
theorem bounds_15_29251 : exactInterval 15 29251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29251 : oddCount 29251 15 = 5 ∧ acceleratedOrbit 15 29251 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29251) = 3 ^ 5 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29251.1, data_15_29251.2]

/-- Complete interval computation for depth 15, residue 29252. -/
theorem bounds_15_29252 : exactInterval 15 29252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29252 : oddCount 29252 15 = 7 ∧ acceleratedOrbit 15 29252 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29252) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29252.1, data_15_29252.2]

/-- Complete interval computation for depth 15, residue 29253. -/
theorem bounds_15_29253 : exactInterval 15 29253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29253 : oddCount 29253 15 = 7 ∧ acceleratedOrbit 15 29253 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29253) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29253.1, data_15_29253.2]

/-- Complete interval computation for depth 15, residue 29254. -/
theorem bounds_15_29254 : exactInterval 15 29254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29254 : oddCount 29254 15 = 7 ∧ acceleratedOrbit 15 29254 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29254) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29254.1, data_15_29254.2]

/-- Complete interval computation for depth 15, residue 29255. -/
theorem bounds_15_29255 : exactInterval 15 29255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29255 : oddCount 29255 15 = 9 ∧ acceleratedOrbit 15 29255 = 17576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29255) = 3 ^ 9 * m + 17576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29255.1, data_15_29255.2]

/-- Complete interval computation for depth 15, residue 29256. -/
theorem bounds_15_29256 : exactInterval 15 29256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29256 : oddCount 29256 15 = 7 ∧ acceleratedOrbit 15 29256 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29256) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29256.1, data_15_29256.2]

/-- Complete interval computation for depth 15, residue 29257. -/
theorem bounds_15_29257 : exactInterval 15 29257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29257 : oddCount 29257 15 = 10 ∧ acceleratedOrbit 15 29257 = 52730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29257) = 3 ^ 10 * m + 52730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29257.1, data_15_29257.2]

/-- Complete interval computation for depth 15, residue 29258. -/
theorem bounds_15_29258 : exactInterval 15 29258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29258 : oddCount 29258 15 = 7 ∧ acceleratedOrbit 15 29258 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29258) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29258.1, data_15_29258.2]

/-- Complete interval computation for depth 15, residue 29259. -/
theorem bounds_15_29259 : exactInterval 15 29259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29259 : oddCount 29259 15 = 7 ∧ acceleratedOrbit 15 29259 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29259) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29259.1, data_15_29259.2]

/-- Complete interval computation for depth 15, residue 29260. -/
theorem bounds_15_29260 : exactInterval 15 29260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29260 : oddCount 29260 15 = 7 ∧ acceleratedOrbit 15 29260 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29260) = 3 ^ 7 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29260.1, data_15_29260.2]

end Collatz.Research.PassageAtlas.Batch0893
