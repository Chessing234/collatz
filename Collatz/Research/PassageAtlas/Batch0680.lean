import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0680

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22249. -/
theorem bounds_15_22249 : exactInterval 15 22249 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22249 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22249) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22249 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22249 : oddCount 22249 15 = 9 ∧ acceleratedOrbit 15 22249 = 13366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22249 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22249) = 3 ^ 9 * m + 13366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22249.1, data_15_22249.2]

/-- Complete interval computation for depth 15, residue 22250. -/
theorem bounds_15_22250 : exactInterval 15 22250 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22250 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22250) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22250 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22250 : oddCount 22250 15 = 6 ∧ acceleratedOrbit 15 22250 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22250 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22250) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22250.1, data_15_22250.2]

/-- Complete interval computation for depth 15, residue 22251. -/
theorem bounds_15_22251 : exactInterval 15 22251 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22251 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22251) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22251 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22251 : oddCount 22251 15 = 8 ∧ acceleratedOrbit 15 22251 = 4456 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22251 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22251) = 3 ^ 8 * m + 4456 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22251.1, data_15_22251.2]

/-- Complete interval computation for depth 15, residue 22252. -/
theorem bounds_15_22252 : exactInterval 15 22252 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22252 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22252) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22252 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22252 : oddCount 22252 15 = 7 ∧ acceleratedOrbit 15 22252 = 1486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22252 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22252) = 3 ^ 7 * m + 1486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22252.1, data_15_22252.2]

/-- Complete interval computation for depth 15, residue 22253. -/
theorem bounds_15_22253 : exactInterval 15 22253 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22253 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22253) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22253 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22253 : oddCount 22253 15 = 7 ∧ acceleratedOrbit 15 22253 = 1486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22253 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22253) = 3 ^ 7 * m + 1486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22253.1, data_15_22253.2]

/-- Complete interval computation for depth 15, residue 22254. -/
theorem bounds_15_22254 : exactInterval 15 22254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22254 : oddCount 22254 15 = 7 ∧ acceleratedOrbit 15 22254 = 1486 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22254) = 3 ^ 7 * m + 1486 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22254.1, data_15_22254.2]

/-- Complete interval computation for depth 15, residue 22255. -/
theorem bounds_15_22255 : exactInterval 15 22255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22255 : oddCount 22255 15 = 9 ∧ acceleratedOrbit 15 22255 = 13369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22255) = 3 ^ 9 * m + 13369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22255.1, data_15_22255.2]

/-- Complete interval computation for depth 15, residue 22256. -/
theorem bounds_15_22256 : exactInterval 15 22256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22256 : oddCount 22256 15 = 7 ∧ acceleratedOrbit 15 22256 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22256) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22256.1, data_15_22256.2]

/-- Complete interval computation for depth 15, residue 22257. -/
theorem bounds_15_22257 : exactInterval 15 22257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22257 : oddCount 22257 15 = 6 ∧ acceleratedOrbit 15 22257 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22257) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22257.1, data_15_22257.2]

/-- Complete interval computation for depth 15, residue 22258. -/
theorem bounds_15_22258 : exactInterval 15 22258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22258 : oddCount 22258 15 = 9 ∧ acceleratedOrbit 15 22258 = 13373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22258) = 3 ^ 9 * m + 13373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22258.1, data_15_22258.2]

/-- Complete interval computation for depth 15, residue 22259. -/
theorem bounds_15_22259 : exactInterval 15 22259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22259 : oddCount 22259 15 = 9 ∧ acceleratedOrbit 15 22259 = 13373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22259) = 3 ^ 9 * m + 13373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22259.1, data_15_22259.2]

/-- Complete interval computation for depth 15, residue 22260. -/
theorem bounds_15_22260 : exactInterval 15 22260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22260 : oddCount 22260 15 = 7 ∧ acceleratedOrbit 15 22260 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22260) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22260.1, data_15_22260.2]

/-- Complete interval computation for depth 15, residue 22261. -/
theorem bounds_15_22261 : exactInterval 15 22261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22261 : oddCount 22261 15 = 7 ∧ acceleratedOrbit 15 22261 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22261) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22261.1, data_15_22261.2]

/-- Complete interval computation for depth 15, residue 22262. -/
theorem bounds_15_22262 : exactInterval 15 22262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22262 : oddCount 22262 15 = 9 ∧ acceleratedOrbit 15 22262 = 13375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22262) = 3 ^ 9 * m + 13375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22262.1, data_15_22262.2]

/-- Complete interval computation for depth 15, residue 22263. -/
theorem bounds_15_22263 : exactInterval 15 22263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22263 : oddCount 22263 15 = 9 ∧ acceleratedOrbit 15 22263 = 13375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22263) = 3 ^ 9 * m + 13375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22263.1, data_15_22263.2]

/-- Complete interval computation for depth 15, residue 22264. -/
theorem bounds_15_22264 : exactInterval 15 22264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22264 : oddCount 22264 15 = 7 ∧ acceleratedOrbit 15 22264 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22264) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22264.1, data_15_22264.2]

/-- Complete interval computation for depth 15, residue 22265. -/
theorem bounds_15_22265 : exactInterval 15 22265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22265 : oddCount 22265 15 = 7 ∧ acceleratedOrbit 15 22265 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22265) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22265.1, data_15_22265.2]

/-- Complete interval computation for depth 15, residue 22266. -/
theorem bounds_15_22266 : exactInterval 15 22266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22266 : oddCount 22266 15 = 7 ∧ acceleratedOrbit 15 22266 = 1487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22266) = 3 ^ 7 * m + 1487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22266.1, data_15_22266.2]

/-- Complete interval computation for depth 15, residue 22267. -/
theorem bounds_15_22267 : exactInterval 15 22267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22267 : oddCount 22267 15 = 8 ∧ acceleratedOrbit 15 22267 = 4459 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22267) = 3 ^ 8 * m + 4459 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22267.1, data_15_22267.2]

/-- Complete interval computation for depth 15, residue 22268. -/
theorem bounds_15_22268 : exactInterval 15 22268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22268 : oddCount 22268 15 = 11 ∧ acceleratedOrbit 15 22268 = 120406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22268) = 3 ^ 11 * m + 120406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22268.1, data_15_22268.2]

/-- Complete interval computation for depth 15, residue 22269. -/
theorem bounds_15_22269 : exactInterval 15 22269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22269 : oddCount 22269 15 = 11 ∧ acceleratedOrbit 15 22269 = 120406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22269) = 3 ^ 11 * m + 120406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22269.1, data_15_22269.2]

/-- Complete interval computation for depth 15, residue 22270. -/
theorem bounds_15_22270 : exactInterval 15 22270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22270 : oddCount 22270 15 = 11 ∧ acceleratedOrbit 15 22270 = 120406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22270) = 3 ^ 11 * m + 120406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22270.1, data_15_22270.2]

/-- Complete interval computation for depth 15, residue 22271. -/
theorem bounds_15_22271 : exactInterval 15 22271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22271 : oddCount 22271 15 = 13 ∧ acceleratedOrbit 15 22271 = 1083644 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22271) = 3 ^ 13 * m + 1083644 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22271.1, data_15_22271.2]

/-- Complete interval computation for depth 15, residue 22272. -/
theorem bounds_15_22272 : exactInterval 15 22272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22272 : oddCount 22272 15 = 4 ∧ acceleratedOrbit 15 22272 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22272) = 3 ^ 4 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22272.1, data_15_22272.2]

/-- Complete interval computation for depth 15, residue 22273. -/
theorem bounds_15_22273 : exactInterval 15 22273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22273 : oddCount 22273 15 = 6 ∧ acceleratedOrbit 15 22273 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22273) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22273.1, data_15_22273.2]

/-- Complete interval computation for depth 15, residue 22274. -/
theorem bounds_15_22274 : exactInterval 15 22274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22274 : oddCount 22274 15 = 9 ∧ acceleratedOrbit 15 22274 = 13385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22274) = 3 ^ 9 * m + 13385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22274.1, data_15_22274.2]

/-- Complete interval computation for depth 15, residue 22275. -/
theorem bounds_15_22275 : exactInterval 15 22275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22275 : oddCount 22275 15 = 9 ∧ acceleratedOrbit 15 22275 = 13385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22275) = 3 ^ 9 * m + 13385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22275.1, data_15_22275.2]

/-- Complete interval computation for depth 15, residue 22276. -/
theorem bounds_15_22276 : exactInterval 15 22276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22276 : oddCount 22276 15 = 6 ∧ acceleratedOrbit 15 22276 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22276) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22276.1, data_15_22276.2]

/-- Complete interval computation for depth 15, residue 22277. -/
theorem bounds_15_22277 : exactInterval 15 22277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22277 : oddCount 22277 15 = 6 ∧ acceleratedOrbit 15 22277 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22277) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22277.1, data_15_22277.2]

/-- Complete interval computation for depth 15, residue 22278. -/
theorem bounds_15_22278 : exactInterval 15 22278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22278 : oddCount 22278 15 = 6 ∧ acceleratedOrbit 15 22278 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22278) = 3 ^ 6 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22278.1, data_15_22278.2]

/-- Complete interval computation for depth 15, residue 22279. -/
theorem bounds_15_22279 : exactInterval 15 22279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22279 : oddCount 22279 15 = 9 ∧ acceleratedOrbit 15 22279 = 13385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22279) = 3 ^ 9 * m + 13385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22279.1, data_15_22279.2]

/-- Complete interval computation for depth 15, residue 22280. -/
theorem bounds_15_22280 : exactInterval 15 22280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22280 : oddCount 22280 15 = 8 ∧ acceleratedOrbit 15 22280 = 4465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22280) = 3 ^ 8 * m + 4465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22280.1, data_15_22280.2]

/-- Complete interval computation for depth 15, residue 22281. -/
theorem bounds_15_22281 : exactInterval 15 22281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22281 : oddCount 22281 15 = 11 ∧ acceleratedOrbit 15 22281 = 120467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22281) = 3 ^ 11 * m + 120467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22281.1, data_15_22281.2]

end Collatz.Research.PassageAtlas.Batch0680
