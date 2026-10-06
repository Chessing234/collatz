import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0710

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23232. -/
theorem bounds_15_23232 : exactInterval 15 23232 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23232 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23232) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23232 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23232 : oddCount 23232 15 = 5 ∧ acceleratedOrbit 15 23232 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23232 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23232) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23232.1, data_15_23232.2]

/-- Complete interval computation for depth 15, residue 23233. -/
theorem bounds_15_23233 : exactInterval 15 23233 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23233 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23233) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23233 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23233 : oddCount 23233 15 = 7 ∧ acceleratedOrbit 15 23233 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23233 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23233) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23233.1, data_15_23233.2]

/-- Complete interval computation for depth 15, residue 23234. -/
theorem bounds_15_23234 : exactInterval 15 23234 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23234 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23234) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23234 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23234 : oddCount 23234 15 = 6 ∧ acceleratedOrbit 15 23234 = 517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23234 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23234) = 3 ^ 6 * m + 517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23234.1, data_15_23234.2]

/-- Complete interval computation for depth 15, residue 23235. -/
theorem bounds_15_23235 : exactInterval 15 23235 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23235 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23235) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23235 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23235 : oddCount 23235 15 = 6 ∧ acceleratedOrbit 15 23235 = 517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23235 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23235) = 3 ^ 6 * m + 517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23235.1, data_15_23235.2]

/-- Complete interval computation for depth 15, residue 23236. -/
theorem bounds_15_23236 : exactInterval 15 23236 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23236 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23236) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23236 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23236 : oddCount 23236 15 = 5 ∧ acceleratedOrbit 15 23236 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23236 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23236) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23236.1, data_15_23236.2]

/-- Complete interval computation for depth 15, residue 23237. -/
theorem bounds_15_23237 : exactInterval 15 23237 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23237 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23237) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23237 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23237 : oddCount 23237 15 = 5 ∧ acceleratedOrbit 15 23237 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23237 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23237) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23237.1, data_15_23237.2]

/-- Complete interval computation for depth 15, residue 23238. -/
theorem bounds_15_23238 : exactInterval 15 23238 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23238 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23238) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23238 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23238 : oddCount 23238 15 = 5 ∧ acceleratedOrbit 15 23238 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23238 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23238) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23238.1, data_15_23238.2]

/-- Complete interval computation for depth 15, residue 23239. -/
theorem bounds_15_23239 : exactInterval 15 23239 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23239 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23239) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23239 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23239 : oddCount 23239 15 = 8 ∧ acceleratedOrbit 15 23239 = 4654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23239 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23239) = 3 ^ 8 * m + 4654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23239.1, data_15_23239.2]

/-- Complete interval computation for depth 15, residue 23240. -/
theorem bounds_15_23240 : exactInterval 15 23240 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23240 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23240) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23240 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23240 : oddCount 23240 15 = 5 ∧ acceleratedOrbit 15 23240 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23240 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23240) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23240.1, data_15_23240.2]

/-- Complete interval computation for depth 15, residue 23241. -/
theorem bounds_15_23241 : exactInterval 15 23241 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23241 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23241) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23241 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23241 : oddCount 23241 15 = 7 ∧ acceleratedOrbit 15 23241 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23241 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23241) = 3 ^ 7 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23241.1, data_15_23241.2]

/-- Complete interval computation for depth 15, residue 23242. -/
theorem bounds_15_23242 : exactInterval 15 23242 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23242 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23242) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23242 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23242 : oddCount 23242 15 = 5 ∧ acceleratedOrbit 15 23242 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23242 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23242) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23242.1, data_15_23242.2]

/-- Complete interval computation for depth 15, residue 23243. -/
theorem bounds_15_23243 : exactInterval 15 23243 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23243 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23243) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23243 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23243 : oddCount 23243 15 = 8 ∧ acceleratedOrbit 15 23243 = 4655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23243 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23243) = 3 ^ 8 * m + 4655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23243.1, data_15_23243.2]

/-- Complete interval computation for depth 15, residue 23244. -/
theorem bounds_15_23244 : exactInterval 15 23244 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23244 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23244) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23244 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23244 : oddCount 23244 15 = 5 ∧ acceleratedOrbit 15 23244 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23244 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23244) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23244.1, data_15_23244.2]

/-- Complete interval computation for depth 15, residue 23245. -/
theorem bounds_15_23245 : exactInterval 15 23245 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23245 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23245) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23245 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23245 : oddCount 23245 15 = 5 ∧ acceleratedOrbit 15 23245 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23245 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23245) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23245.1, data_15_23245.2]

/-- Complete interval computation for depth 15, residue 23246. -/
theorem bounds_15_23246 : exactInterval 15 23246 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23246 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23246) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23246 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23246 : oddCount 23246 15 = 12 ∧ acceleratedOrbit 15 23246 = 377054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23246 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23246) = 3 ^ 12 * m + 377054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23246.1, data_15_23246.2]

/-- Complete interval computation for depth 15, residue 23247. -/
theorem bounds_15_23247 : exactInterval 15 23247 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23247 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23247) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23247 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23247 : oddCount 23247 15 = 12 ∧ acceleratedOrbit 15 23247 = 377054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23247 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23247) = 3 ^ 12 * m + 377054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23247.1, data_15_23247.2]

/-- Complete interval computation for depth 15, residue 23248. -/
theorem bounds_15_23248 : exactInterval 15 23248 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23248 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23248) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23248 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23248 : oddCount 23248 15 = 5 ∧ acceleratedOrbit 15 23248 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23248 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23248) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23248.1, data_15_23248.2]

/-- Complete interval computation for depth 15, residue 23249. -/
theorem bounds_15_23249 : exactInterval 15 23249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23249 : oddCount 23249 15 = 8 ∧ acceleratedOrbit 15 23249 = 4657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23249) = 3 ^ 8 * m + 4657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23249.1, data_15_23249.2]

/-- Complete interval computation for depth 15, residue 23250. -/
theorem bounds_15_23250 : exactInterval 15 23250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23250 : oddCount 23250 15 = 8 ∧ acceleratedOrbit 15 23250 = 4657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23250) = 3 ^ 8 * m + 4657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23250.1, data_15_23250.2]

/-- Complete interval computation for depth 15, residue 23251. -/
theorem bounds_15_23251 : exactInterval 15 23251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23251 : oddCount 23251 15 = 8 ∧ acceleratedOrbit 15 23251 = 4657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23251) = 3 ^ 8 * m + 4657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23251.1, data_15_23251.2]

/-- Complete interval computation for depth 15, residue 23252. -/
theorem bounds_15_23252 : exactInterval 15 23252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23252 : oddCount 23252 15 = 5 ∧ acceleratedOrbit 15 23252 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23252) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23252.1, data_15_23252.2]

/-- Complete interval computation for depth 15, residue 23253. -/
theorem bounds_15_23253 : exactInterval 15 23253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23253 : oddCount 23253 15 = 5 ∧ acceleratedOrbit 15 23253 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23253) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23253.1, data_15_23253.2]

/-- Complete interval computation for depth 15, residue 23254. -/
theorem bounds_15_23254 : exactInterval 15 23254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23254 : oddCount 23254 15 = 9 ∧ acceleratedOrbit 15 23254 = 13972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23254) = 3 ^ 9 * m + 13972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23254.1, data_15_23254.2]

/-- Complete interval computation for depth 15, residue 23255. -/
theorem bounds_15_23255 : exactInterval 15 23255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23255 : oddCount 23255 15 = 9 ∧ acceleratedOrbit 15 23255 = 13972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23255) = 3 ^ 9 * m + 13972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23255.1, data_15_23255.2]

/-- Complete interval computation for depth 15, residue 23256. -/
theorem bounds_15_23256 : exactInterval 15 23256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23256 : oddCount 23256 15 = 7 ∧ acceleratedOrbit 15 23256 = 1553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23256) = 3 ^ 7 * m + 1553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23256.1, data_15_23256.2]

/-- Complete interval computation for depth 15, residue 23257. -/
theorem bounds_15_23257 : exactInterval 15 23257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23257 : oddCount 23257 15 = 5 ∧ acceleratedOrbit 15 23257 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23257) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23257.1, data_15_23257.2]

/-- Complete interval computation for depth 15, residue 23258. -/
theorem bounds_15_23258 : exactInterval 15 23258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23258 : oddCount 23258 15 = 7 ∧ acceleratedOrbit 15 23258 = 1553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23258) = 3 ^ 7 * m + 1553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23258.1, data_15_23258.2]

/-- Complete interval computation for depth 15, residue 23259. -/
theorem bounds_15_23259 : exactInterval 15 23259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23259 : oddCount 23259 15 = 11 ∧ acceleratedOrbit 15 23259 = 125752 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23259) = 3 ^ 11 * m + 125752 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23259.1, data_15_23259.2]

/-- Complete interval computation for depth 15, residue 23260. -/
theorem bounds_15_23260 : exactInterval 15 23260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23260 : oddCount 23260 15 = 7 ∧ acceleratedOrbit 15 23260 = 1553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23260) = 3 ^ 7 * m + 1553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23260.1, data_15_23260.2]

/-- Complete interval computation for depth 15, residue 23261. -/
theorem bounds_15_23261 : exactInterval 15 23261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23261 : oddCount 23261 15 = 7 ∧ acceleratedOrbit 15 23261 = 1553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23261) = 3 ^ 7 * m + 1553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23261.1, data_15_23261.2]

/-- Complete interval computation for depth 15, residue 23262. -/
theorem bounds_15_23262 : exactInterval 15 23262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23262 : oddCount 23262 15 = 9 ∧ acceleratedOrbit 15 23262 = 13976 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23262) = 3 ^ 9 * m + 13976 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23262.1, data_15_23262.2]

/-- Complete interval computation for depth 15, residue 23263. -/
theorem bounds_15_23263 : exactInterval 15 23263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23263 : oddCount 23263 15 = 9 ∧ acceleratedOrbit 15 23263 = 13976 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23263) = 3 ^ 9 * m + 13976 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23263.1, data_15_23263.2]

/-- Complete interval computation for depth 15, residue 23264. -/
theorem bounds_15_23264 : exactInterval 15 23264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23264 : oddCount 23264 15 = 5 ∧ acceleratedOrbit 15 23264 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23264) = 3 ^ 5 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23264.1, data_15_23264.2]

end Collatz.Research.PassageAtlas.Batch0710
