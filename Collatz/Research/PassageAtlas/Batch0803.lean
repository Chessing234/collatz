import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0803

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26279. -/
theorem bounds_15_26279 : exactInterval 15 26279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26279 : oddCount 26279 15 = 7 ∧ acceleratedOrbit 15 26279 = 1754 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26279) = 3 ^ 7 * m + 1754 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26279.1, data_15_26279.2]

/-- Complete interval computation for depth 15, residue 26280. -/
theorem bounds_15_26280 : exactInterval 15 26280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26280 : oddCount 26280 15 = 3 ∧ acceleratedOrbit 15 26280 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26280) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26280.1, data_15_26280.2]

/-- Complete interval computation for depth 15, residue 26281. -/
theorem bounds_15_26281 : exactInterval 15 26281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26281 : oddCount 26281 15 = 11 ∧ acceleratedOrbit 15 26281 = 142087 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26281) = 3 ^ 11 * m + 142087 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26281.1, data_15_26281.2]

/-- Complete interval computation for depth 15, residue 26282. -/
theorem bounds_15_26282 : exactInterval 15 26282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26282 : oddCount 26282 15 = 3 ∧ acceleratedOrbit 15 26282 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26282) = 3 ^ 3 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26282.1, data_15_26282.2]

/-- Complete interval computation for depth 15, residue 26283. -/
theorem bounds_15_26283 : exactInterval 15 26283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26283 : oddCount 26283 15 = 9 ∧ acceleratedOrbit 15 26283 = 15790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26283) = 3 ^ 9 * m + 15790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26283.1, data_15_26283.2]

/-- Complete interval computation for depth 15, residue 26284. -/
theorem bounds_15_26284 : exactInterval 15 26284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26284 : oddCount 26284 15 = 10 ∧ acceleratedOrbit 15 26284 = 47384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26284) = 3 ^ 10 * m + 47384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26284.1, data_15_26284.2]

/-- Complete interval computation for depth 15, residue 26285. -/
theorem bounds_15_26285 : exactInterval 15 26285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26285 : oddCount 26285 15 = 10 ∧ acceleratedOrbit 15 26285 = 47384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26285) = 3 ^ 10 * m + 47384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26285.1, data_15_26285.2]

/-- Complete interval computation for depth 15, residue 26286. -/
theorem bounds_15_26286 : exactInterval 15 26286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26286 : oddCount 26286 15 = 10 ∧ acceleratedOrbit 15 26286 = 47384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26286) = 3 ^ 10 * m + 47384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26286.1, data_15_26286.2]

/-- Complete interval computation for depth 15, residue 26287. -/
theorem bounds_15_26287 : exactInterval 15 26287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26287 : oddCount 26287 15 = 10 ∧ acceleratedOrbit 15 26287 = 47375 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26287) = 3 ^ 10 * m + 47375 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26287.1, data_15_26287.2]

/-- Complete interval computation for depth 15, residue 26288. -/
theorem bounds_15_26288 : exactInterval 15 26288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26288 : oddCount 26288 15 = 7 ∧ acceleratedOrbit 15 26288 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26288) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26288.1, data_15_26288.2]

/-- Complete interval computation for depth 15, residue 26289. -/
theorem bounds_15_26289 : exactInterval 15 26289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26289 : oddCount 26289 15 = 4 ∧ acceleratedOrbit 15 26289 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26289) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26289.1, data_15_26289.2]

/-- Complete interval computation for depth 15, residue 26290. -/
theorem bounds_15_26290 : exactInterval 15 26290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26290 : oddCount 26290 15 = 4 ∧ acceleratedOrbit 15 26290 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26290) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26290.1, data_15_26290.2]

/-- Complete interval computation for depth 15, residue 26291. -/
theorem bounds_15_26291 : exactInterval 15 26291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26291 : oddCount 26291 15 = 4 ∧ acceleratedOrbit 15 26291 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26291) = 3 ^ 4 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26291.1, data_15_26291.2]

/-- Complete interval computation for depth 15, residue 26292. -/
theorem bounds_15_26292 : exactInterval 15 26292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26292 : oddCount 26292 15 = 7 ∧ acceleratedOrbit 15 26292 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26292) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26292.1, data_15_26292.2]

/-- Complete interval computation for depth 15, residue 26293. -/
theorem bounds_15_26293 : exactInterval 15 26293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26293 : oddCount 26293 15 = 7 ∧ acceleratedOrbit 15 26293 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26293) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26293.1, data_15_26293.2]

/-- Complete interval computation for depth 15, residue 26294. -/
theorem bounds_15_26294 : exactInterval 15 26294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26294 : oddCount 26294 15 = 9 ∧ acceleratedOrbit 15 26294 = 15797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26294) = 3 ^ 9 * m + 15797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26294.1, data_15_26294.2]

/-- Complete interval computation for depth 15, residue 26295. -/
theorem bounds_15_26295 : exactInterval 15 26295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26295 : oddCount 26295 15 = 9 ∧ acceleratedOrbit 15 26295 = 15797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26295) = 3 ^ 9 * m + 15797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26295.1, data_15_26295.2]

/-- Complete interval computation for depth 15, residue 26296. -/
theorem bounds_15_26296 : exactInterval 15 26296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26296 : oddCount 26296 15 = 7 ∧ acceleratedOrbit 15 26296 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26296) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26296.1, data_15_26296.2]

/-- Complete interval computation for depth 15, residue 26297. -/
theorem bounds_15_26297 : exactInterval 15 26297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26297 : oddCount 26297 15 = 8 ∧ acceleratedOrbit 15 26297 = 5267 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26297) = 3 ^ 8 * m + 5267 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26297.1, data_15_26297.2]

/-- Complete interval computation for depth 15, residue 26298. -/
theorem bounds_15_26298 : exactInterval 15 26298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26298 : oddCount 26298 15 = 7 ∧ acceleratedOrbit 15 26298 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26298) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26298.1, data_15_26298.2]

/-- Complete interval computation for depth 15, residue 26299. -/
theorem bounds_15_26299 : exactInterval 15 26299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26299 : oddCount 26299 15 = 8 ∧ acceleratedOrbit 15 26299 = 5267 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26299) = 3 ^ 8 * m + 5267 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26299.1, data_15_26299.2]

/-- Complete interval computation for depth 15, residue 26300. -/
theorem bounds_15_26300 : exactInterval 15 26300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26300 : oddCount 26300 15 = 7 ∧ acceleratedOrbit 15 26300 = 1756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26300) = 3 ^ 7 * m + 1756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26300.1, data_15_26300.2]

/-- Complete interval computation for depth 15, residue 26301. -/
theorem bounds_15_26301 : exactInterval 15 26301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26301 : oddCount 26301 15 = 7 ∧ acceleratedOrbit 15 26301 = 1756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26301) = 3 ^ 7 * m + 1756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26301.1, data_15_26301.2]

/-- Complete interval computation for depth 15, residue 26302. -/
theorem bounds_15_26302 : exactInterval 15 26302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26302 : oddCount 26302 15 = 7 ∧ acceleratedOrbit 15 26302 = 1756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26302) = 3 ^ 7 * m + 1756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26302.1, data_15_26302.2]

/-- Complete interval computation for depth 15, residue 26303. -/
theorem bounds_15_26303 : exactInterval 15 26303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26303 : oddCount 26303 15 = 10 ∧ acceleratedOrbit 15 26303 = 47402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26303) = 3 ^ 10 * m + 47402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26303.1, data_15_26303.2]

/-- Complete interval computation for depth 15, residue 26304. -/
theorem bounds_15_26304 : exactInterval 15 26304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26304 : oddCount 26304 15 = 6 ∧ acceleratedOrbit 15 26304 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26304) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26304.1, data_15_26304.2]

/-- Complete interval computation for depth 15, residue 26305. -/
theorem bounds_15_26305 : exactInterval 15 26305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26305 : oddCount 26305 15 = 7 ∧ acceleratedOrbit 15 26305 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26305) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26305.1, data_15_26305.2]

/-- Complete interval computation for depth 15, residue 26306. -/
theorem bounds_15_26306 : exactInterval 15 26306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26306 : oddCount 26306 15 = 9 ∧ acceleratedOrbit 15 26306 = 15805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26306) = 3 ^ 9 * m + 15805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26306.1, data_15_26306.2]

/-- Complete interval computation for depth 15, residue 26307. -/
theorem bounds_15_26307 : exactInterval 15 26307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26307 : oddCount 26307 15 = 9 ∧ acceleratedOrbit 15 26307 = 15805 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26307) = 3 ^ 9 * m + 15805 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26307.1, data_15_26307.2]

/-- Complete interval computation for depth 15, residue 26308. -/
theorem bounds_15_26308 : exactInterval 15 26308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26308 : oddCount 26308 15 = 6 ∧ acceleratedOrbit 15 26308 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26308) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26308.1, data_15_26308.2]

/-- Complete interval computation for depth 15, residue 26309. -/
theorem bounds_15_26309 : exactInterval 15 26309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26309 : oddCount 26309 15 = 6 ∧ acceleratedOrbit 15 26309 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26309) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26309.1, data_15_26309.2]

/-- Complete interval computation for depth 15, residue 26310. -/
theorem bounds_15_26310 : exactInterval 15 26310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26310 : oddCount 26310 15 = 6 ∧ acceleratedOrbit 15 26310 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26310) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26310.1, data_15_26310.2]

/-- Complete interval computation for depth 15, residue 26311. -/
theorem bounds_15_26311 : exactInterval 15 26311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26311 : oddCount 26311 15 = 7 ∧ acceleratedOrbit 15 26311 = 1757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26311) = 3 ^ 7 * m + 1757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26311.1, data_15_26311.2]

end Collatz.Research.PassageAtlas.Batch0803
