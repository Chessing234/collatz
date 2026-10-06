import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0191

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6225. -/
theorem bounds_15_6225 : exactInterval 15 6225 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6225 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6225) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6225 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6225 : oddCount 6225 15 = 7 ∧ acceleratedOrbit 15 6225 = 416 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6225 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6225) = 3 ^ 7 * m + 416 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6225.1, data_15_6225.2]

/-- Complete interval computation for depth 15, residue 6226. -/
theorem bounds_15_6226 : exactInterval 15 6226 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6226 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6226) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6226 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6226 : oddCount 6226 15 = 9 ∧ acceleratedOrbit 15 6226 = 3743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6226 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6226) = 3 ^ 9 * m + 3743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6226.1, data_15_6226.2]

/-- Complete interval computation for depth 15, residue 6227. -/
theorem bounds_15_6227 : exactInterval 15 6227 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6227 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6227) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6227 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6227 : oddCount 6227 15 = 9 ∧ acceleratedOrbit 15 6227 = 3743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6227 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6227) = 3 ^ 9 * m + 3743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6227.1, data_15_6227.2]

/-- Complete interval computation for depth 15, residue 6228. -/
theorem bounds_15_6228 : exactInterval 15 6228 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6228 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6228) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6228 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6228 : oddCount 6228 15 = 5 ∧ acceleratedOrbit 15 6228 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6228 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6228) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6228.1, data_15_6228.2]

/-- Complete interval computation for depth 15, residue 6229. -/
theorem bounds_15_6229 : exactInterval 15 6229 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6229 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6229) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6229 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6229 : oddCount 6229 15 = 5 ∧ acceleratedOrbit 15 6229 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6229 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6229) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6229.1, data_15_6229.2]

/-- Complete interval computation for depth 15, residue 6230. -/
theorem bounds_15_6230 : exactInterval 15 6230 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6230 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6230) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6230 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6230 : oddCount 6230 15 = 6 ∧ acceleratedOrbit 15 6230 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6230 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6230) = 3 ^ 6 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6230.1, data_15_6230.2]

/-- Complete interval computation for depth 15, residue 6231. -/
theorem bounds_15_6231 : exactInterval 15 6231 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6231 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6231) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6231 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6231 : oddCount 6231 15 = 6 ∧ acceleratedOrbit 15 6231 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6231 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6231) = 3 ^ 6 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6231.1, data_15_6231.2]

/-- Complete interval computation for depth 15, residue 6232. -/
theorem bounds_15_6232 : exactInterval 15 6232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6232 : oddCount 6232 15 = 7 ∧ acceleratedOrbit 15 6232 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6232) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6232.1, data_15_6232.2]

/-- Complete interval computation for depth 15, residue 6233. -/
theorem bounds_15_6233 : exactInterval 15 6233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6233 : oddCount 6233 15 = 6 ∧ acceleratedOrbit 15 6233 = 139 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6233) = 3 ^ 6 * m + 139 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6233.1, data_15_6233.2]

/-- Complete interval computation for depth 15, residue 6234. -/
theorem bounds_15_6234 : exactInterval 15 6234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6234 : oddCount 6234 15 = 7 ∧ acceleratedOrbit 15 6234 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6234) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6234.1, data_15_6234.2]

/-- Complete interval computation for depth 15, residue 6235. -/
theorem bounds_15_6235 : exactInterval 15 6235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6235 : oddCount 6235 15 = 11 ∧ acceleratedOrbit 15 6235 = 33716 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6235) = 3 ^ 11 * m + 33716 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6235.1, data_15_6235.2]

/-- Complete interval computation for depth 15, residue 6236. -/
theorem bounds_15_6236 : exactInterval 15 6236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6236 : oddCount 6236 15 = 7 ∧ acceleratedOrbit 15 6236 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6236) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6236.1, data_15_6236.2]

/-- Complete interval computation for depth 15, residue 6237. -/
theorem bounds_15_6237 : exactInterval 15 6237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6237 : oddCount 6237 15 = 7 ∧ acceleratedOrbit 15 6237 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6237) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6237.1, data_15_6237.2]

/-- Complete interval computation for depth 15, residue 6238. -/
theorem bounds_15_6238 : exactInterval 15 6238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6238 : oddCount 6238 15 = 8 ∧ acceleratedOrbit 15 6238 = 1250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6238) = 3 ^ 8 * m + 1250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6238.1, data_15_6238.2]

/-- Complete interval computation for depth 15, residue 6239. -/
theorem bounds_15_6239 : exactInterval 15 6239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6239 : oddCount 6239 15 = 8 ∧ acceleratedOrbit 15 6239 = 1250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6239) = 3 ^ 8 * m + 1250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6239.1, data_15_6239.2]

/-- Complete interval computation for depth 15, residue 6240. -/
theorem bounds_15_6240 : exactInterval 15 6240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6240 : oddCount 6240 15 = 5 ∧ acceleratedOrbit 15 6240 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6240) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6240.1, data_15_6240.2]

/-- Complete interval computation for depth 15, residue 6241. -/
theorem bounds_15_6241 : exactInterval 15 6241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6241 : oddCount 6241 15 = 9 ∧ acceleratedOrbit 15 6241 = 3752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6241) = 3 ^ 9 * m + 3752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6241.1, data_15_6241.2]

/-- Complete interval computation for depth 15, residue 6242. -/
theorem bounds_15_6242 : exactInterval 15 6242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6242 : oddCount 6242 15 = 7 ∧ acceleratedOrbit 15 6242 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6242) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6242.1, data_15_6242.2]

/-- Complete interval computation for depth 15, residue 6243. -/
theorem bounds_15_6243 : exactInterval 15 6243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6243 : oddCount 6243 15 = 7 ∧ acceleratedOrbit 15 6243 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6243) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6243.1, data_15_6243.2]

/-- Complete interval computation for depth 15, residue 6244. -/
theorem bounds_15_6244 : exactInterval 15 6244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6244 : oddCount 6244 15 = 7 ∧ acceleratedOrbit 15 6244 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6244) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6244.1, data_15_6244.2]

/-- Complete interval computation for depth 15, residue 6245. -/
theorem bounds_15_6245 : exactInterval 15 6245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6245 : oddCount 6245 15 = 7 ∧ acceleratedOrbit 15 6245 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6245) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6245.1, data_15_6245.2]

/-- Complete interval computation for depth 15, residue 6246. -/
theorem bounds_15_6246 : exactInterval 15 6246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6246 : oddCount 6246 15 = 7 ∧ acceleratedOrbit 15 6246 = 418 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6246) = 3 ^ 7 * m + 418 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6246.1, data_15_6246.2]

/-- Complete interval computation for depth 15, residue 6247. -/
theorem bounds_15_6247 : exactInterval 15 6247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6247 : oddCount 6247 15 = 10 ∧ acceleratedOrbit 15 6247 = 11260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6247) = 3 ^ 10 * m + 11260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6247.1, data_15_6247.2]

/-- Complete interval computation for depth 15, residue 6248. -/
theorem bounds_15_6248 : exactInterval 15 6248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6248 : oddCount 6248 15 = 5 ∧ acceleratedOrbit 15 6248 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6248) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6248.1, data_15_6248.2]

/-- Complete interval computation for depth 15, residue 6249. -/
theorem bounds_15_6249 : exactInterval 15 6249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6249 : oddCount 6249 15 = 8 ∧ acceleratedOrbit 15 6249 = 1252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6249) = 3 ^ 8 * m + 1252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6249.1, data_15_6249.2]

/-- Complete interval computation for depth 15, residue 6250. -/
theorem bounds_15_6250 : exactInterval 15 6250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6250 : oddCount 6250 15 = 5 ∧ acceleratedOrbit 15 6250 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6250) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6250.1, data_15_6250.2]

/-- Complete interval computation for depth 15, residue 6251. -/
theorem bounds_15_6251 : exactInterval 15 6251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6251 : oddCount 6251 15 = 10 ∧ acceleratedOrbit 15 6251 = 11269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6251) = 3 ^ 10 * m + 11269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6251.1, data_15_6251.2]

/-- Complete interval computation for depth 15, residue 6252. -/
theorem bounds_15_6252 : exactInterval 15 6252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6252 : oddCount 6252 15 = 8 ∧ acceleratedOrbit 15 6252 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6252) = 3 ^ 8 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6252.1, data_15_6252.2]

/-- Complete interval computation for depth 15, residue 6253. -/
theorem bounds_15_6253 : exactInterval 15 6253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6253 : oddCount 6253 15 = 8 ∧ acceleratedOrbit 15 6253 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6253) = 3 ^ 8 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6253.1, data_15_6253.2]

/-- Complete interval computation for depth 15, residue 6254. -/
theorem bounds_15_6254 : exactInterval 15 6254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6254 : oddCount 6254 15 = 8 ∧ acceleratedOrbit 15 6254 = 1253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6254) = 3 ^ 8 * m + 1253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6254.1, data_15_6254.2]

/-- Complete interval computation for depth 15, residue 6255. -/
theorem bounds_15_6255 : exactInterval 15 6255 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6255) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6255 : oddCount 6255 15 = 9 ∧ acceleratedOrbit 15 6255 = 3758 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6255) = 3 ^ 9 * m + 3758 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6255.1, data_15_6255.2]

/-- Complete interval computation for depth 15, residue 6256. -/
theorem bounds_15_6256 : exactInterval 15 6256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6256 : oddCount 6256 15 = 5 ∧ acceleratedOrbit 15 6256 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6256) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6256.1, data_15_6256.2]

/-- Complete interval computation for depth 15, residue 6257. -/
theorem bounds_15_6257 : exactInterval 15 6257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6257 : oddCount 6257 15 = 5 ∧ acceleratedOrbit 15 6257 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6257) = 3 ^ 5 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6257.1, data_15_6257.2]

end Collatz.Research.PassageAtlas.Batch0191
