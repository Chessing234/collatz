import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0436

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 14254. -/
theorem bounds_15_14254 : exactInterval 15 14254 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14254 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14254) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14254 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14254 : oddCount 14254 15 = 10 ∧ acceleratedOrbit 15 14254 = 25697 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14254 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14254) = 3 ^ 10 * m + 25697 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14254.1, data_15_14254.2]

/-- Complete interval computation for depth 15, residue 14255. -/
theorem bounds_15_14255 : exactInterval 15 14255 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14255 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14255) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14255 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14255 : oddCount 14255 15 = 8 ∧ acceleratedOrbit 15 14255 = 2855 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14255 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14255) = 3 ^ 8 * m + 2855 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14255.1, data_15_14255.2]

/-- Complete interval computation for depth 15, residue 14256. -/
theorem bounds_15_14256 : exactInterval 15 14256 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14256 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14256) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14256 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14256 : oddCount 14256 15 = 8 ∧ acceleratedOrbit 15 14256 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14256 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14256) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14256.1, data_15_14256.2]

/-- Complete interval computation for depth 15, residue 14257. -/
theorem bounds_15_14257 : exactInterval 15 14257 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14257 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14257) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14257 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14257 : oddCount 14257 15 = 5 ∧ acceleratedOrbit 15 14257 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14257 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14257) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14257.1, data_15_14257.2]

/-- Complete interval computation for depth 15, residue 14258. -/
theorem bounds_15_14258 : exactInterval 15 14258 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14258 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14258) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14258 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14258 : oddCount 14258 15 = 5 ∧ acceleratedOrbit 15 14258 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14258 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14258) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14258.1, data_15_14258.2]

/-- Complete interval computation for depth 15, residue 14259. -/
theorem bounds_15_14259 : exactInterval 15 14259 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14259 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14259) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14259 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14259 : oddCount 14259 15 = 5 ∧ acceleratedOrbit 15 14259 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14259 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14259) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14259.1, data_15_14259.2]

/-- Complete interval computation for depth 15, residue 14260. -/
theorem bounds_15_14260 : exactInterval 15 14260 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14260 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14260) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14260 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14260 : oddCount 14260 15 = 8 ∧ acceleratedOrbit 15 14260 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14260 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14260) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14260.1, data_15_14260.2]

/-- Complete interval computation for depth 15, residue 14261. -/
theorem bounds_15_14261 : exactInterval 15 14261 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14261 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14261) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14261 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14261 : oddCount 14261 15 = 8 ∧ acceleratedOrbit 15 14261 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14261 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14261) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14261.1, data_15_14261.2]

/-- Complete interval computation for depth 15, residue 14262. -/
theorem bounds_15_14262 : exactInterval 15 14262 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14262 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14262) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14262 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14262 : oddCount 14262 15 = 8 ∧ acceleratedOrbit 15 14262 = 2857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14262 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14262) = 3 ^ 8 * m + 2857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14262.1, data_15_14262.2]

/-- Complete interval computation for depth 15, residue 14263. -/
theorem bounds_15_14263 : exactInterval 15 14263 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14263 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14263) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14263 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14263 : oddCount 14263 15 = 8 ∧ acceleratedOrbit 15 14263 = 2857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14263 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14263) = 3 ^ 8 * m + 2857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14263.1, data_15_14263.2]

/-- Complete interval computation for depth 15, residue 14264. -/
theorem bounds_15_14264 : exactInterval 15 14264 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14264 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14264) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14264 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14264 : oddCount 14264 15 = 8 ∧ acceleratedOrbit 15 14264 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14264 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14264) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14264.1, data_15_14264.2]

/-- Complete interval computation for depth 15, residue 14265. -/
theorem bounds_15_14265 : exactInterval 15 14265 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14265 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14265) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14265 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14265 : oddCount 14265 15 = 7 ∧ acceleratedOrbit 15 14265 = 953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14265 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14265) = 3 ^ 7 * m + 953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14265.1, data_15_14265.2]

/-- Complete interval computation for depth 15, residue 14266. -/
theorem bounds_15_14266 : exactInterval 15 14266 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14266 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14266) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14266 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14266 : oddCount 14266 15 = 8 ∧ acceleratedOrbit 15 14266 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14266 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14266) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14266.1, data_15_14266.2]

/-- Complete interval computation for depth 15, residue 14267. -/
theorem bounds_15_14267 : exactInterval 15 14267 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14267 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14267) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14267 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14267 : oddCount 14267 15 = 7 ∧ acceleratedOrbit 15 14267 = 953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14267 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14267) = 3 ^ 7 * m + 953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14267.1, data_15_14267.2]

/-- Complete interval computation for depth 15, residue 14268. -/
theorem bounds_15_14268 : exactInterval 15 14268 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14268 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14268) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14268 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14268 : oddCount 14268 15 = 10 ∧ acceleratedOrbit 15 14268 = 25721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14268 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14268) = 3 ^ 10 * m + 25721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14268.1, data_15_14268.2]

/-- Complete interval computation for depth 15, residue 14269. -/
theorem bounds_15_14269 : exactInterval 15 14269 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14269 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14269) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14269 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14269 : oddCount 14269 15 = 10 ∧ acceleratedOrbit 15 14269 = 25721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14269 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14269) = 3 ^ 10 * m + 25721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14269.1, data_15_14269.2]

/-- Complete interval computation for depth 15, residue 14270. -/
theorem bounds_15_14270 : exactInterval 15 14270 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14270 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14270) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14270 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14270 : oddCount 14270 15 = 10 ∧ acceleratedOrbit 15 14270 = 25721 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14270 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14270) = 3 ^ 10 * m + 25721 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14270.1, data_15_14270.2]

/-- Complete interval computation for depth 15, residue 14271. -/
theorem bounds_15_14271 : exactInterval 15 14271 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14271 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14271) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14271 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14271 : oddCount 14271 15 = 9 ∧ acceleratedOrbit 15 14271 = 8573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14271 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14271) = 3 ^ 9 * m + 8573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14271.1, data_15_14271.2]

/-- Complete interval computation for depth 15, residue 14272. -/
theorem bounds_15_14272 : exactInterval 15 14272 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14272 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14272) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14272 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14272 : oddCount 14272 15 = 6 ∧ acceleratedOrbit 15 14272 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14272 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14272) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14272.1, data_15_14272.2]

/-- Complete interval computation for depth 15, residue 14273. -/
theorem bounds_15_14273 : exactInterval 15 14273 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14273 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14273) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14273 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14273 : oddCount 14273 15 = 8 ∧ acceleratedOrbit 15 14273 = 2861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14273 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14273) = 3 ^ 8 * m + 2861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14273.1, data_15_14273.2]

/-- Complete interval computation for depth 15, residue 14274. -/
theorem bounds_15_14274 : exactInterval 15 14274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14274 : oddCount 14274 15 = 7 ∧ acceleratedOrbit 15 14274 = 953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14274) = 3 ^ 7 * m + 953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14274.1, data_15_14274.2]

/-- Complete interval computation for depth 15, residue 14275. -/
theorem bounds_15_14275 : exactInterval 15 14275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14275 : oddCount 14275 15 = 7 ∧ acceleratedOrbit 15 14275 = 953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14275) = 3 ^ 7 * m + 953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14275.1, data_15_14275.2]

/-- Complete interval computation for depth 15, residue 14276. -/
theorem bounds_15_14276 : exactInterval 15 14276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14276 : oddCount 14276 15 = 6 ∧ acceleratedOrbit 15 14276 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14276) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14276.1, data_15_14276.2]

/-- Complete interval computation for depth 15, residue 14277. -/
theorem bounds_15_14277 : exactInterval 15 14277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14277 : oddCount 14277 15 = 6 ∧ acceleratedOrbit 15 14277 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14277) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14277.1, data_15_14277.2]

/-- Complete interval computation for depth 15, residue 14278. -/
theorem bounds_15_14278 : exactInterval 15 14278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14278 : oddCount 14278 15 = 6 ∧ acceleratedOrbit 15 14278 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14278) = 3 ^ 6 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14278.1, data_15_14278.2]

/-- Complete interval computation for depth 15, residue 14279. -/
theorem bounds_15_14279 : exactInterval 15 14279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14279 : oddCount 14279 15 = 9 ∧ acceleratedOrbit 15 14279 = 8579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14279) = 3 ^ 9 * m + 8579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14279.1, data_15_14279.2]

/-- Complete interval computation for depth 15, residue 14280. -/
theorem bounds_15_14280 : exactInterval 15 14280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14280 : oddCount 14280 15 = 5 ∧ acceleratedOrbit 15 14280 = 106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14280) = 3 ^ 5 * m + 106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14280.1, data_15_14280.2]

/-- Complete interval computation for depth 15, residue 14281. -/
theorem bounds_15_14281 : exactInterval 15 14281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14281 : oddCount 14281 15 = 9 ∧ acceleratedOrbit 15 14281 = 8581 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14281) = 3 ^ 9 * m + 8581 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14281.1, data_15_14281.2]

/-- Complete interval computation for depth 15, residue 14282. -/
theorem bounds_15_14282 : exactInterval 15 14282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14282 : oddCount 14282 15 = 5 ∧ acceleratedOrbit 15 14282 = 106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14282) = 3 ^ 5 * m + 106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14282.1, data_15_14282.2]

/-- Complete interval computation for depth 15, residue 14283. -/
theorem bounds_15_14283 : exactInterval 15 14283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14283 : oddCount 14283 15 = 5 ∧ acceleratedOrbit 15 14283 = 106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14283) = 3 ^ 5 * m + 106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14283.1, data_15_14283.2]

/-- Complete interval computation for depth 15, residue 14284. -/
theorem bounds_15_14284 : exactInterval 15 14284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14284 : oddCount 14284 15 = 5 ∧ acceleratedOrbit 15 14284 = 106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14284) = 3 ^ 5 * m + 106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14284.1, data_15_14284.2]

/-- Complete interval computation for depth 15, residue 14285. -/
theorem bounds_15_14285 : exactInterval 15 14285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_14285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 14285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_14285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_14285 : oddCount 14285 15 = 5 ∧ acceleratedOrbit 15 14285 = 106 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_14285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 14285) = 3 ^ 5 * m + 106 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_14285.1, data_15_14285.2]

end Collatz.Research.PassageAtlas.Batch0436
