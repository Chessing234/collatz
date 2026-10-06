import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0528

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17268. -/
theorem bounds_15_17268 : exactInterval 15 17268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17268 : oddCount 17268 15 = 7 ∧ acceleratedOrbit 15 17268 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17268) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17268.1, data_15_17268.2]

/-- Complete interval computation for depth 15, residue 17269. -/
theorem bounds_15_17269 : exactInterval 15 17269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17269 : oddCount 17269 15 = 7 ∧ acceleratedOrbit 15 17269 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17269) = 3 ^ 7 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17269.1, data_15_17269.2]

/-- Complete interval computation for depth 15, residue 17270. -/
theorem bounds_15_17270 : exactInterval 15 17270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17270 : oddCount 17270 15 = 7 ∧ acceleratedOrbit 15 17270 = 1153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17270) = 3 ^ 7 * m + 1153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17270.1, data_15_17270.2]

/-- Complete interval computation for depth 15, residue 17271. -/
theorem bounds_15_17271 : exactInterval 15 17271 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17271) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17271 : oddCount 17271 15 = 7 ∧ acceleratedOrbit 15 17271 = 1153 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17271) = 3 ^ 7 * m + 1153 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17271.1, data_15_17271.2]

/-- Complete interval computation for depth 15, residue 17272. -/
theorem bounds_15_17272 : exactInterval 15 17272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17272 : oddCount 17272 15 = 9 ∧ acceleratedOrbit 15 17272 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17272) = 3 ^ 9 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17272.1, data_15_17272.2]

/-- Complete interval computation for depth 15, residue 17273. -/
theorem bounds_15_17273 : exactInterval 15 17273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17273 : oddCount 17273 15 = 12 ∧ acceleratedOrbit 15 17273 = 280178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17273) = 3 ^ 12 * m + 280178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17273.1, data_15_17273.2]

/-- Complete interval computation for depth 15, residue 17274. -/
theorem bounds_15_17274 : exactInterval 15 17274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17274 : oddCount 17274 15 = 9 ∧ acceleratedOrbit 15 17274 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17274) = 3 ^ 9 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17274.1, data_15_17274.2]

/-- Complete interval computation for depth 15, residue 17275. -/
theorem bounds_15_17275 : exactInterval 15 17275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17275 : oddCount 17275 15 = 9 ∧ acceleratedOrbit 15 17275 = 10378 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17275) = 3 ^ 9 * m + 10378 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17275.1, data_15_17275.2]

/-- Complete interval computation for depth 15, residue 17276. -/
theorem bounds_15_17276 : exactInterval 15 17276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17276 : oddCount 17276 15 = 9 ∧ acceleratedOrbit 15 17276 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17276) = 3 ^ 9 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17276.1, data_15_17276.2]

/-- Complete interval computation for depth 15, residue 17277. -/
theorem bounds_15_17277 : exactInterval 15 17277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17277 : oddCount 17277 15 = 9 ∧ acceleratedOrbit 15 17277 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17277) = 3 ^ 9 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17277.1, data_15_17277.2]

/-- Complete interval computation for depth 15, residue 17278. -/
theorem bounds_15_17278 : exactInterval 15 17278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17278 : oddCount 17278 15 = 11 ∧ acceleratedOrbit 15 17278 = 93419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17278) = 3 ^ 11 * m + 93419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17278.1, data_15_17278.2]

/-- Complete interval computation for depth 15, residue 17279. -/
theorem bounds_15_17279 : exactInterval 15 17279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17279 : oddCount 17279 15 = 11 ∧ acceleratedOrbit 15 17279 = 93419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17279) = 3 ^ 11 * m + 93419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17279.1, data_15_17279.2]

/-- Complete interval computation for depth 15, residue 17280. -/
theorem bounds_15_17280 : exactInterval 15 17280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17280 : oddCount 17280 15 = 4 ∧ acceleratedOrbit 15 17280 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17280) = 3 ^ 4 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17280.1, data_15_17280.2]

/-- Complete interval computation for depth 15, residue 17281. -/
theorem bounds_15_17281 : exactInterval 15 17281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17281 : oddCount 17281 15 = 8 ∧ acceleratedOrbit 15 17281 = 3461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17281) = 3 ^ 8 * m + 3461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17281.1, data_15_17281.2]

/-- Complete interval computation for depth 15, residue 17282. -/
theorem bounds_15_17282 : exactInterval 15 17282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17282 : oddCount 17282 15 = 9 ∧ acceleratedOrbit 15 17282 = 10388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17282) = 3 ^ 9 * m + 10388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17282.1, data_15_17282.2]

/-- Complete interval computation for depth 15, residue 17283. -/
theorem bounds_15_17283 : exactInterval 15 17283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17283 : oddCount 17283 15 = 9 ∧ acceleratedOrbit 15 17283 = 10388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17283) = 3 ^ 9 * m + 10388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17283.1, data_15_17283.2]

/-- Complete interval computation for depth 15, residue 17284. -/
theorem bounds_15_17284 : exactInterval 15 17284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17284 : oddCount 17284 15 = 9 ∧ acceleratedOrbit 15 17284 = 10388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17284) = 3 ^ 9 * m + 10388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17284.1, data_15_17284.2]

/-- Complete interval computation for depth 15, residue 17285. -/
theorem bounds_15_17285 : exactInterval 15 17285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17285 : oddCount 17285 15 = 9 ∧ acceleratedOrbit 15 17285 = 10388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17285) = 3 ^ 9 * m + 10388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17285.1, data_15_17285.2]

/-- Complete interval computation for depth 15, residue 17286. -/
theorem bounds_15_17286 : exactInterval 15 17286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17286 : oddCount 17286 15 = 9 ∧ acceleratedOrbit 15 17286 = 10388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17286) = 3 ^ 9 * m + 10388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17286.1, data_15_17286.2]

/-- Complete interval computation for depth 15, residue 17287. -/
theorem bounds_15_17287 : exactInterval 15 17287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17287 : oddCount 17287 15 = 9 ∧ acceleratedOrbit 15 17287 = 10388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17287) = 3 ^ 9 * m + 10388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17287.1, data_15_17287.2]

/-- Complete interval computation for depth 15, residue 17288. -/
theorem bounds_15_17288 : exactInterval 15 17288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17288 : oddCount 17288 15 = 4 ∧ acceleratedOrbit 15 17288 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17288) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17288.1, data_15_17288.2]

/-- Complete interval computation for depth 15, residue 17289. -/
theorem bounds_15_17289 : exactInterval 15 17289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17289 : oddCount 17289 15 = 10 ∧ acceleratedOrbit 15 17289 = 31160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17289) = 3 ^ 10 * m + 31160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17289.1, data_15_17289.2]

/-- Complete interval computation for depth 15, residue 17290. -/
theorem bounds_15_17290 : exactInterval 15 17290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17290 : oddCount 17290 15 = 4 ∧ acceleratedOrbit 15 17290 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17290) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17290.1, data_15_17290.2]

/-- Complete interval computation for depth 15, residue 17291. -/
theorem bounds_15_17291 : exactInterval 15 17291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17291 : oddCount 17291 15 = 11 ∧ acceleratedOrbit 15 17291 = 93494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17291) = 3 ^ 11 * m + 93494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17291.1, data_15_17291.2]

/-- Complete interval computation for depth 15, residue 17292. -/
theorem bounds_15_17292 : exactInterval 15 17292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17292 : oddCount 17292 15 = 4 ∧ acceleratedOrbit 15 17292 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17292) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17292.1, data_15_17292.2]

/-- Complete interval computation for depth 15, residue 17293. -/
theorem bounds_15_17293 : exactInterval 15 17293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17293 : oddCount 17293 15 = 4 ∧ acceleratedOrbit 15 17293 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17293) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17293.1, data_15_17293.2]

/-- Complete interval computation for depth 15, residue 17294. -/
theorem bounds_15_17294 : exactInterval 15 17294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17294 : oddCount 17294 15 = 8 ∧ acceleratedOrbit 15 17294 = 3464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17294) = 3 ^ 8 * m + 3464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17294.1, data_15_17294.2]

/-- Complete interval computation for depth 15, residue 17295. -/
theorem bounds_15_17295 : exactInterval 15 17295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17295 : oddCount 17295 15 = 8 ∧ acceleratedOrbit 15 17295 = 3464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17295) = 3 ^ 8 * m + 3464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17295.1, data_15_17295.2]

/-- Complete interval computation for depth 15, residue 17296. -/
theorem bounds_15_17296 : exactInterval 15 17296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17296 : oddCount 17296 15 = 6 ∧ acceleratedOrbit 15 17296 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17296) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17296.1, data_15_17296.2]

/-- Complete interval computation for depth 15, residue 17297. -/
theorem bounds_15_17297 : exactInterval 15 17297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17297 : oddCount 17297 15 = 6 ∧ acceleratedOrbit 15 17297 = 385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17297) = 3 ^ 6 * m + 385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17297.1, data_15_17297.2]

/-- Complete interval computation for depth 15, residue 17298. -/
theorem bounds_15_17298 : exactInterval 15 17298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17298 : oddCount 17298 15 = 6 ∧ acceleratedOrbit 15 17298 = 385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17298) = 3 ^ 6 * m + 385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17298.1, data_15_17298.2]

/-- Complete interval computation for depth 15, residue 17299. -/
theorem bounds_15_17299 : exactInterval 15 17299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17299 : oddCount 17299 15 = 6 ∧ acceleratedOrbit 15 17299 = 385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17299) = 3 ^ 6 * m + 385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17299.1, data_15_17299.2]

/-- Complete interval computation for depth 15, residue 17300. -/
theorem bounds_15_17300 : exactInterval 15 17300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17300 : oddCount 17300 15 = 6 ∧ acceleratedOrbit 15 17300 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17300) = 3 ^ 6 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17300.1, data_15_17300.2]

end Collatz.Research.PassageAtlas.Batch0528
