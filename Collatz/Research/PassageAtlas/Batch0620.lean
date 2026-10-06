import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0620

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20283. -/
theorem bounds_15_20283 : exactInterval 15 20283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20283 : oddCount 20283 15 = 8 ∧ acceleratedOrbit 15 20283 = 4063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20283) = 3 ^ 8 * m + 4063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20283.1, data_15_20283.2]

/-- Complete interval computation for depth 15, residue 20284. -/
theorem bounds_15_20284 : exactInterval 15 20284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20284 : oddCount 20284 15 = 8 ∧ acceleratedOrbit 15 20284 = 4063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20284) = 3 ^ 8 * m + 4063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20284.1, data_15_20284.2]

/-- Complete interval computation for depth 15, residue 20285. -/
theorem bounds_15_20285 : exactInterval 15 20285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20285 : oddCount 20285 15 = 8 ∧ acceleratedOrbit 15 20285 = 4063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20285) = 3 ^ 8 * m + 4063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20285.1, data_15_20285.2]

/-- Complete interval computation for depth 15, residue 20286. -/
theorem bounds_15_20286 : exactInterval 15 20286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20286 : oddCount 20286 15 = 9 ∧ acceleratedOrbit 15 20286 = 12187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20286) = 3 ^ 9 * m + 12187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20286.1, data_15_20286.2]

/-- Complete interval computation for depth 15, residue 20287. -/
theorem bounds_15_20287 : exactInterval 15 20287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20287 : oddCount 20287 15 = 9 ∧ acceleratedOrbit 15 20287 = 12187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20287) = 3 ^ 9 * m + 12187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20287.1, data_15_20287.2]

/-- Complete interval computation for depth 15, residue 20288. -/
theorem bounds_15_20288 : exactInterval 15 20288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20288 : oddCount 20288 15 = 5 ∧ acceleratedOrbit 15 20288 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20288) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20288.1, data_15_20288.2]

/-- Complete interval computation for depth 15, residue 20289. -/
theorem bounds_15_20289 : exactInterval 15 20289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20289 : oddCount 20289 15 = 6 ∧ acceleratedOrbit 15 20289 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20289) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20289.1, data_15_20289.2]

/-- Complete interval computation for depth 15, residue 20290. -/
theorem bounds_15_20290 : exactInterval 15 20290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20290 : oddCount 20290 15 = 6 ∧ acceleratedOrbit 15 20290 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20290) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20290.1, data_15_20290.2]

/-- Complete interval computation for depth 15, residue 20291. -/
theorem bounds_15_20291 : exactInterval 15 20291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20291 : oddCount 20291 15 = 6 ∧ acceleratedOrbit 15 20291 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20291) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20291.1, data_15_20291.2]

/-- Complete interval computation for depth 15, residue 20292. -/
theorem bounds_15_20292 : exactInterval 15 20292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20292 : oddCount 20292 15 = 6 ∧ acceleratedOrbit 15 20292 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20292) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20292.1, data_15_20292.2]

/-- Complete interval computation for depth 15, residue 20293. -/
theorem bounds_15_20293 : exactInterval 15 20293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20293 : oddCount 20293 15 = 6 ∧ acceleratedOrbit 15 20293 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20293) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20293.1, data_15_20293.2]

/-- Complete interval computation for depth 15, residue 20294. -/
theorem bounds_15_20294 : exactInterval 15 20294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20294 : oddCount 20294 15 = 6 ∧ acceleratedOrbit 15 20294 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20294) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20294.1, data_15_20294.2]

/-- Complete interval computation for depth 15, residue 20295. -/
theorem bounds_15_20295 : exactInterval 15 20295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20295 : oddCount 20295 15 = 8 ∧ acceleratedOrbit 15 20295 = 4064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20295) = 3 ^ 8 * m + 4064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20295.1, data_15_20295.2]

/-- Complete interval computation for depth 15, residue 20296. -/
theorem bounds_15_20296 : exactInterval 15 20296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20296 : oddCount 20296 15 = 8 ∧ acceleratedOrbit 15 20296 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20296) = 3 ^ 8 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20296.1, data_15_20296.2]

/-- Complete interval computation for depth 15, residue 20297. -/
theorem bounds_15_20297 : exactInterval 15 20297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20297 : oddCount 20297 15 = 7 ∧ acceleratedOrbit 15 20297 = 1355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20297) = 3 ^ 7 * m + 1355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20297.1, data_15_20297.2]

/-- Complete interval computation for depth 15, residue 20298. -/
theorem bounds_15_20298 : exactInterval 15 20298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20298 : oddCount 20298 15 = 8 ∧ acceleratedOrbit 15 20298 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20298) = 3 ^ 8 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20298.1, data_15_20298.2]

/-- Complete interval computation for depth 15, residue 20299. -/
theorem bounds_15_20299 : exactInterval 15 20299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20299 : oddCount 20299 15 = 6 ∧ acceleratedOrbit 15 20299 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20299) = 3 ^ 6 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20299.1, data_15_20299.2]

/-- Complete interval computation for depth 15, residue 20300. -/
theorem bounds_15_20300 : exactInterval 15 20300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20300 : oddCount 20300 15 = 8 ∧ acceleratedOrbit 15 20300 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20300) = 3 ^ 8 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20300.1, data_15_20300.2]

/-- Complete interval computation for depth 15, residue 20301. -/
theorem bounds_15_20301 : exactInterval 15 20301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20301 : oddCount 20301 15 = 8 ∧ acceleratedOrbit 15 20301 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20301) = 3 ^ 8 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20301.1, data_15_20301.2]

/-- Complete interval computation for depth 15, residue 20302. -/
theorem bounds_15_20302 : exactInterval 15 20302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20302 : oddCount 20302 15 = 9 ∧ acceleratedOrbit 15 20302 = 12197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20302) = 3 ^ 9 * m + 12197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20302.1, data_15_20302.2]

/-- Complete interval computation for depth 15, residue 20303. -/
theorem bounds_15_20303 : exactInterval 15 20303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20303 : oddCount 20303 15 = 9 ∧ acceleratedOrbit 15 20303 = 12197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20303) = 3 ^ 9 * m + 12197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20303.1, data_15_20303.2]

/-- Complete interval computation for depth 15, residue 20304. -/
theorem bounds_15_20304 : exactInterval 15 20304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20304 : oddCount 20304 15 = 5 ∧ acceleratedOrbit 15 20304 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20304) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20304.1, data_15_20304.2]

/-- Complete interval computation for depth 15, residue 20305. -/
theorem bounds_15_20305 : exactInterval 15 20305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20305 : oddCount 20305 15 = 8 ∧ acceleratedOrbit 15 20305 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20305) = 3 ^ 8 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20305.1, data_15_20305.2]

/-- Complete interval computation for depth 15, residue 20306. -/
theorem bounds_15_20306 : exactInterval 15 20306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20306 : oddCount 20306 15 = 11 ∧ acceleratedOrbit 15 20306 = 109795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20306) = 3 ^ 11 * m + 109795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20306.1, data_15_20306.2]

/-- Complete interval computation for depth 15, residue 20307. -/
theorem bounds_15_20307 : exactInterval 15 20307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20307 : oddCount 20307 15 = 11 ∧ acceleratedOrbit 15 20307 = 109795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20307) = 3 ^ 11 * m + 109795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20307.1, data_15_20307.2]

/-- Complete interval computation for depth 15, residue 20308. -/
theorem bounds_15_20308 : exactInterval 15 20308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20308 : oddCount 20308 15 = 5 ∧ acceleratedOrbit 15 20308 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20308) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20308.1, data_15_20308.2]

/-- Complete interval computation for depth 15, residue 20309. -/
theorem bounds_15_20309 : exactInterval 15 20309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20309 : oddCount 20309 15 = 5 ∧ acceleratedOrbit 15 20309 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20309) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20309.1, data_15_20309.2]

/-- Complete interval computation for depth 15, residue 20310. -/
theorem bounds_15_20310 : exactInterval 15 20310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20310 : oddCount 20310 15 = 10 ∧ acceleratedOrbit 15 20310 = 36611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20310) = 3 ^ 10 * m + 36611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20310.1, data_15_20310.2]

/-- Complete interval computation for depth 15, residue 20311. -/
theorem bounds_15_20311 : exactInterval 15 20311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20311 : oddCount 20311 15 = 10 ∧ acceleratedOrbit 15 20311 = 36611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20311) = 3 ^ 10 * m + 36611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20311.1, data_15_20311.2]

/-- Complete interval computation for depth 15, residue 20312. -/
theorem bounds_15_20312 : exactInterval 15 20312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20312 : oddCount 20312 15 = 8 ∧ acceleratedOrbit 15 20312 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20312) = 3 ^ 8 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20312.1, data_15_20312.2]

/-- Complete interval computation for depth 15, residue 20313. -/
theorem bounds_15_20313 : exactInterval 15 20313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20313 : oddCount 20313 15 = 8 ∧ acceleratedOrbit 15 20313 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20313) = 3 ^ 8 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20313.1, data_15_20313.2]

/-- Complete interval computation for depth 15, residue 20314. -/
theorem bounds_15_20314 : exactInterval 15 20314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20314 : oddCount 20314 15 = 8 ∧ acceleratedOrbit 15 20314 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20314) = 3 ^ 8 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20314.1, data_15_20314.2]

/-- Complete interval computation for depth 15, residue 20315. -/
theorem bounds_15_20315 : exactInterval 15 20315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20315 : oddCount 20315 15 = 12 ∧ acceleratedOrbit 15 20315 = 329507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20315) = 3 ^ 12 * m + 329507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20315.1, data_15_20315.2]

end Collatz.Research.PassageAtlas.Batch0620
