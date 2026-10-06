import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0313

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10223. -/
theorem bounds_15_10223 : exactInterval 15 10223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10223 : oddCount 10223 15 = 9 ∧ acceleratedOrbit 15 10223 = 6142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10223) = 3 ^ 9 * m + 6142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10223.1, data_15_10223.2]

/-- Complete interval computation for depth 15, residue 10224. -/
theorem bounds_15_10224 : exactInterval 15 10224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10224 : oddCount 10224 15 = 9 ∧ acceleratedOrbit 15 10224 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10224) = 3 ^ 9 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10224.1, data_15_10224.2]

/-- Complete interval computation for depth 15, residue 10225. -/
theorem bounds_15_10225 : exactInterval 15 10225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10225 : oddCount 10225 15 = 8 ∧ acceleratedOrbit 15 10225 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10225) = 3 ^ 8 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10225.1, data_15_10225.2]

/-- Complete interval computation for depth 15, residue 10226. -/
theorem bounds_15_10226 : exactInterval 15 10226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10226 : oddCount 10226 15 = 9 ∧ acceleratedOrbit 15 10226 = 6146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10226) = 3 ^ 9 * m + 6146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10226.1, data_15_10226.2]

/-- Complete interval computation for depth 15, residue 10227. -/
theorem bounds_15_10227 : exactInterval 15 10227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10227 : oddCount 10227 15 = 9 ∧ acceleratedOrbit 15 10227 = 6146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10227) = 3 ^ 9 * m + 6146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10227.1, data_15_10227.2]

/-- Complete interval computation for depth 15, residue 10228. -/
theorem bounds_15_10228 : exactInterval 15 10228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10228 : oddCount 10228 15 = 9 ∧ acceleratedOrbit 15 10228 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10228) = 3 ^ 9 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10228.1, data_15_10228.2]

/-- Complete interval computation for depth 15, residue 10229. -/
theorem bounds_15_10229 : exactInterval 15 10229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10229 : oddCount 10229 15 = 9 ∧ acceleratedOrbit 15 10229 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10229) = 3 ^ 9 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10229.1, data_15_10229.2]

/-- Complete interval computation for depth 15, residue 10230. -/
theorem bounds_15_10230 : exactInterval 15 10230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10230 : oddCount 10230 15 = 7 ∧ acceleratedOrbit 15 10230 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10230) = 3 ^ 7 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10230.1, data_15_10230.2]

/-- Complete interval computation for depth 15, residue 10231. -/
theorem bounds_15_10231 : exactInterval 15 10231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10231 : oddCount 10231 15 = 7 ∧ acceleratedOrbit 15 10231 = 683 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10231) = 3 ^ 7 * m + 683 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10231.1, data_15_10231.2]

/-- Complete interval computation for depth 15, residue 10232. -/
theorem bounds_15_10232 : exactInterval 15 10232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10232 : oddCount 10232 15 = 9 ∧ acceleratedOrbit 15 10232 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10232) = 3 ^ 9 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10232.1, data_15_10232.2]

/-- Complete interval computation for depth 15, residue 10233. -/
theorem bounds_15_10233 : exactInterval 15 10233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10233 : oddCount 10233 15 = 9 ∧ acceleratedOrbit 15 10233 = 6149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10233) = 3 ^ 9 * m + 6149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10233.1, data_15_10233.2]

/-- Complete interval computation for depth 15, residue 10234. -/
theorem bounds_15_10234 : exactInterval 15 10234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10234 : oddCount 10234 15 = 9 ∧ acceleratedOrbit 15 10234 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10234) = 3 ^ 9 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10234.1, data_15_10234.2]

/-- Complete interval computation for depth 15, residue 10235. -/
theorem bounds_15_10235 : exactInterval 15 10235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10235 : oddCount 10235 15 = 11 ∧ acceleratedOrbit 15 10235 = 55343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10235) = 3 ^ 11 * m + 55343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10235.1, data_15_10235.2]

/-- Complete interval computation for depth 15, residue 10236. -/
theorem bounds_15_10236 : exactInterval 15 10236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10236 : oddCount 10236 15 = 12 ∧ acceleratedOrbit 15 10236 = 166076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10236) = 3 ^ 12 * m + 166076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10236.1, data_15_10236.2]

/-- Complete interval computation for depth 15, residue 10237. -/
theorem bounds_15_10237 : exactInterval 15 10237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10237 : oddCount 10237 15 = 12 ∧ acceleratedOrbit 15 10237 = 166076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10237) = 3 ^ 12 * m + 166076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10237.1, data_15_10237.2]

/-- Complete interval computation for depth 15, residue 10238. -/
theorem bounds_15_10238 : exactInterval 15 10238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10238 : oddCount 10238 15 = 12 ∧ acceleratedOrbit 15 10238 = 166076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10238) = 3 ^ 12 * m + 166076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10238.1, data_15_10238.2]

/-- Complete interval computation for depth 15, residue 10239. -/
theorem bounds_15_10239 : exactInterval 15 10239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10239 : oddCount 10239 15 = 13 ∧ acceleratedOrbit 15 10239 = 498226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10239) = 3 ^ 13 * m + 498226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10239.1, data_15_10239.2]

/-- Complete interval computation for depth 15, residue 10240. -/
theorem bounds_15_10240 : exactInterval 15 10240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10240 : oddCount 10240 15 = 1 ∧ acceleratedOrbit 15 10240 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10240) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10240.1, data_15_10240.2]

/-- Complete interval computation for depth 15, residue 10241. -/
theorem bounds_15_10241 : exactInterval 15 10241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10241 : oddCount 10241 15 = 10 ∧ acceleratedOrbit 15 10241 = 18467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10241) = 3 ^ 10 * m + 18467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10241.1, data_15_10241.2]

/-- Complete interval computation for depth 15, residue 10242. -/
theorem bounds_15_10242 : exactInterval 15 10242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10242 : oddCount 10242 15 = 5 ∧ acceleratedOrbit 15 10242 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10242) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10242.1, data_15_10242.2]

/-- Complete interval computation for depth 15, residue 10243. -/
theorem bounds_15_10243 : exactInterval 15 10243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10243 : oddCount 10243 15 = 5 ∧ acceleratedOrbit 15 10243 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10243) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10243.1, data_15_10243.2]

/-- Complete interval computation for depth 15, residue 10244. -/
theorem bounds_15_10244 : exactInterval 15 10244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10244 : oddCount 10244 15 = 7 ∧ acceleratedOrbit 15 10244 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10244) = 3 ^ 7 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10244.1, data_15_10244.2]

/-- Complete interval computation for depth 15, residue 10245. -/
theorem bounds_15_10245 : exactInterval 15 10245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10245 : oddCount 10245 15 = 7 ∧ acceleratedOrbit 15 10245 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10245) = 3 ^ 7 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10245.1, data_15_10245.2]

/-- Complete interval computation for depth 15, residue 10246. -/
theorem bounds_15_10246 : exactInterval 15 10246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10246 : oddCount 10246 15 = 7 ∧ acceleratedOrbit 15 10246 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10246) = 3 ^ 7 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10246.1, data_15_10246.2]

/-- Complete interval computation for depth 15, residue 10247. -/
theorem bounds_15_10247 : exactInterval 15 10247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10247 : oddCount 10247 15 = 5 ∧ acceleratedOrbit 15 10247 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10247) = 3 ^ 5 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10247.1, data_15_10247.2]

/-- Complete interval computation for depth 15, residue 10248. -/
theorem bounds_15_10248 : exactInterval 15 10248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10248 : oddCount 10248 15 = 6 ∧ acceleratedOrbit 15 10248 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10248) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10248.1, data_15_10248.2]

/-- Complete interval computation for depth 15, residue 10249. -/
theorem bounds_15_10249 : exactInterval 15 10249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10249 : oddCount 10249 15 = 8 ∧ acceleratedOrbit 15 10249 = 2053 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10249) = 3 ^ 8 * m + 2053 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10249.1, data_15_10249.2]

/-- Complete interval computation for depth 15, residue 10250. -/
theorem bounds_15_10250 : exactInterval 15 10250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10250 : oddCount 10250 15 = 6 ∧ acceleratedOrbit 15 10250 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10250) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10250.1, data_15_10250.2]

/-- Complete interval computation for depth 15, residue 10251. -/
theorem bounds_15_10251 : exactInterval 15 10251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10251 : oddCount 10251 15 = 7 ∧ acceleratedOrbit 15 10251 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10251) = 3 ^ 7 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10251.1, data_15_10251.2]

/-- Complete interval computation for depth 15, residue 10252. -/
theorem bounds_15_10252 : exactInterval 15 10252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10252 : oddCount 10252 15 = 6 ∧ acceleratedOrbit 15 10252 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10252) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10252.1, data_15_10252.2]

/-- Complete interval computation for depth 15, residue 10253. -/
theorem bounds_15_10253 : exactInterval 15 10253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10253 : oddCount 10253 15 = 6 ∧ acceleratedOrbit 15 10253 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10253) = 3 ^ 6 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10253.1, data_15_10253.2]

/-- Complete interval computation for depth 15, residue 10254. -/
theorem bounds_15_10254 : exactInterval 15 10254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10254 : oddCount 10254 15 = 7 ∧ acceleratedOrbit 15 10254 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10254) = 3 ^ 7 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10254.1, data_15_10254.2]

/-- Complete interval computation for depth 15, residue 10255. -/
theorem bounds_15_10255 : exactInterval 15 10255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10255 : oddCount 10255 15 = 7 ∧ acceleratedOrbit 15 10255 = 685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10255) = 3 ^ 7 * m + 685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10255.1, data_15_10255.2]

end Collatz.Research.PassageAtlas.Batch0313
