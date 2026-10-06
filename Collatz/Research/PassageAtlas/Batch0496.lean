import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0496

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16220. -/
theorem bounds_15_16220 : exactInterval 15 16220 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16220 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16220) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16220 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16220 : oddCount 16220 15 = 8 ∧ acceleratedOrbit 15 16220 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16220 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16220) = 3 ^ 8 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16220.1, data_15_16220.2]

/-- Complete interval computation for depth 15, residue 16221. -/
theorem bounds_15_16221 : exactInterval 15 16221 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16221 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16221) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16221 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16221 : oddCount 16221 15 = 8 ∧ acceleratedOrbit 15 16221 = 3250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16221 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16221) = 3 ^ 8 * m + 3250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16221.1, data_15_16221.2]

/-- Complete interval computation for depth 15, residue 16222. -/
theorem bounds_15_16222 : exactInterval 15 16222 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16222 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16222) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16222 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16222 : oddCount 16222 15 = 6 ∧ acceleratedOrbit 15 16222 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16222 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16222) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16222.1, data_15_16222.2]

/-- Complete interval computation for depth 15, residue 16223. -/
theorem bounds_15_16223 : exactInterval 15 16223 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16223 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16223) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16223 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16223 : oddCount 16223 15 = 6 ∧ acceleratedOrbit 15 16223 = 361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16223 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16223) = 3 ^ 6 * m + 361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16223.1, data_15_16223.2]

/-- Complete interval computation for depth 15, residue 16224. -/
theorem bounds_15_16224 : exactInterval 15 16224 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16224 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16224) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16224 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16224 : oddCount 16224 15 = 6 ∧ acceleratedOrbit 15 16224 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16224 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16224) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16224.1, data_15_16224.2]

/-- Complete interval computation for depth 15, residue 16225. -/
theorem bounds_15_16225 : exactInterval 15 16225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16225 : oddCount 16225 15 = 9 ∧ acceleratedOrbit 15 16225 = 9748 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16225) = 3 ^ 9 * m + 9748 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16225.1, data_15_16225.2]

/-- Complete interval computation for depth 15, residue 16226. -/
theorem bounds_15_16226 : exactInterval 15 16226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16226 : oddCount 16226 15 = 5 ∧ acceleratedOrbit 15 16226 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16226) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16226.1, data_15_16226.2]

/-- Complete interval computation for depth 15, residue 16227. -/
theorem bounds_15_16227 : exactInterval 15 16227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16227 : oddCount 16227 15 = 5 ∧ acceleratedOrbit 15 16227 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16227) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16227.1, data_15_16227.2]

/-- Complete interval computation for depth 15, residue 16228. -/
theorem bounds_15_16228 : exactInterval 15 16228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16228 : oddCount 16228 15 = 5 ∧ acceleratedOrbit 15 16228 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16228) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16228.1, data_15_16228.2]

/-- Complete interval computation for depth 15, residue 16229. -/
theorem bounds_15_16229 : exactInterval 15 16229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16229 : oddCount 16229 15 = 5 ∧ acceleratedOrbit 15 16229 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16229) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16229.1, data_15_16229.2]

/-- Complete interval computation for depth 15, residue 16230. -/
theorem bounds_15_16230 : exactInterval 15 16230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16230 : oddCount 16230 15 = 5 ∧ acceleratedOrbit 15 16230 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16230) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16230.1, data_15_16230.2]

/-- Complete interval computation for depth 15, residue 16231. -/
theorem bounds_15_16231 : exactInterval 15 16231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16231 : oddCount 16231 15 = 12 ∧ acceleratedOrbit 15 16231 = 263260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16231) = 3 ^ 12 * m + 263260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16231.1, data_15_16231.2]

/-- Complete interval computation for depth 15, residue 16232. -/
theorem bounds_15_16232 : exactInterval 15 16232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16232 : oddCount 16232 15 = 6 ∧ acceleratedOrbit 15 16232 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16232) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16232.1, data_15_16232.2]

/-- Complete interval computation for depth 15, residue 16233. -/
theorem bounds_15_16233 : exactInterval 15 16233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16233 : oddCount 16233 15 = 8 ∧ acceleratedOrbit 15 16233 = 3251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16233) = 3 ^ 8 * m + 3251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16233.1, data_15_16233.2]

/-- Complete interval computation for depth 15, residue 16234. -/
theorem bounds_15_16234 : exactInterval 15 16234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16234 : oddCount 16234 15 = 6 ∧ acceleratedOrbit 15 16234 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16234) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16234.1, data_15_16234.2]

/-- Complete interval computation for depth 15, residue 16235. -/
theorem bounds_15_16235 : exactInterval 15 16235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16235 : oddCount 16235 15 = 7 ∧ acceleratedOrbit 15 16235 = 1084 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16235) = 3 ^ 7 * m + 1084 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16235.1, data_15_16235.2]

/-- Complete interval computation for depth 15, residue 16236. -/
theorem bounds_15_16236 : exactInterval 15 16236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16236 : oddCount 16236 15 = 8 ∧ acceleratedOrbit 15 16236 = 3253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16236) = 3 ^ 8 * m + 3253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16236.1, data_15_16236.2]

/-- Complete interval computation for depth 15, residue 16237. -/
theorem bounds_15_16237 : exactInterval 15 16237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16237 : oddCount 16237 15 = 8 ∧ acceleratedOrbit 15 16237 = 3253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16237) = 3 ^ 8 * m + 3253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16237.1, data_15_16237.2]

/-- Complete interval computation for depth 15, residue 16238. -/
theorem bounds_15_16238 : exactInterval 15 16238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16238 : oddCount 16238 15 = 8 ∧ acceleratedOrbit 15 16238 = 3253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16238) = 3 ^ 8 * m + 3253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16238.1, data_15_16238.2]

/-- Complete interval computation for depth 15, residue 16239. -/
theorem bounds_15_16239 : exactInterval 15 16239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16239 : oddCount 16239 15 = 10 ∧ acceleratedOrbit 15 16239 = 29267 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16239) = 3 ^ 10 * m + 29267 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16239.1, data_15_16239.2]

/-- Complete interval computation for depth 15, residue 16240. -/
theorem bounds_15_16240 : exactInterval 15 16240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16240 : oddCount 16240 15 = 6 ∧ acceleratedOrbit 15 16240 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16240) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16240.1, data_15_16240.2]

/-- Complete interval computation for depth 15, residue 16241. -/
theorem bounds_15_16241 : exactInterval 15 16241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16241 : oddCount 16241 15 = 6 ∧ acceleratedOrbit 15 16241 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16241) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16241.1, data_15_16241.2]

/-- Complete interval computation for depth 15, residue 16242. -/
theorem bounds_15_16242 : exactInterval 15 16242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16242 : oddCount 16242 15 = 6 ∧ acceleratedOrbit 15 16242 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16242) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16242.1, data_15_16242.2]

/-- Complete interval computation for depth 15, residue 16243. -/
theorem bounds_15_16243 : exactInterval 15 16243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16243 : oddCount 16243 15 = 6 ∧ acceleratedOrbit 15 16243 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16243) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16243.1, data_15_16243.2]

/-- Complete interval computation for depth 15, residue 16244. -/
theorem bounds_15_16244 : exactInterval 15 16244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16244 : oddCount 16244 15 = 6 ∧ acceleratedOrbit 15 16244 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16244) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16244.1, data_15_16244.2]

/-- Complete interval computation for depth 15, residue 16245. -/
theorem bounds_15_16245 : exactInterval 15 16245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16245 : oddCount 16245 15 = 6 ∧ acceleratedOrbit 15 16245 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16245) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16245.1, data_15_16245.2]

/-- Complete interval computation for depth 15, residue 16246. -/
theorem bounds_15_16246 : exactInterval 15 16246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16246 : oddCount 16246 15 = 6 ∧ acceleratedOrbit 15 16246 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16246) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16246.1, data_15_16246.2]

/-- Complete interval computation for depth 15, residue 16247. -/
theorem bounds_15_16247 : exactInterval 15 16247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16247 : oddCount 16247 15 = 6 ∧ acceleratedOrbit 15 16247 = 362 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16247) = 3 ^ 6 * m + 362 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16247.1, data_15_16247.2]

/-- Complete interval computation for depth 15, residue 16248. -/
theorem bounds_15_16248 : exactInterval 15 16248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16248 : oddCount 16248 15 = 7 ∧ acceleratedOrbit 15 16248 = 1085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16248) = 3 ^ 7 * m + 1085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16248.1, data_15_16248.2]

/-- Complete interval computation for depth 15, residue 16249. -/
theorem bounds_15_16249 : exactInterval 15 16249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16249 : oddCount 16249 15 = 8 ∧ acceleratedOrbit 15 16249 = 3254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16249) = 3 ^ 8 * m + 3254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16249.1, data_15_16249.2]

/-- Complete interval computation for depth 15, residue 16250. -/
theorem bounds_15_16250 : exactInterval 15 16250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16250 : oddCount 16250 15 = 7 ∧ acceleratedOrbit 15 16250 = 1085 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16250) = 3 ^ 7 * m + 1085 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16250.1, data_15_16250.2]

/-- Complete interval computation for depth 15, residue 16251. -/
theorem bounds_15_16251 : exactInterval 15 16251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16251 : oddCount 16251 15 = 9 ∧ acceleratedOrbit 15 16251 = 9764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16251) = 3 ^ 9 * m + 9764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16251.1, data_15_16251.2]

end Collatz.Research.PassageAtlas.Batch0496
