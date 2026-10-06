import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0010

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 294. -/
theorem bounds_15_294 : exactInterval 15 294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_294 : oddCount 294 15 = 9 ∧ acceleratedOrbit 15 294 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 294) = 3 ^ 9 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_294.1, data_15_294.2]

/-- Complete interval computation for depth 15, residue 295. -/
theorem bounds_15_295 : exactInterval 15 295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_295 : oddCount 295 15 = 9 ∧ acceleratedOrbit 15 295 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 295) = 3 ^ 9 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_295.1, data_15_295.2]

/-- Complete interval computation for depth 15, residue 296. -/
theorem bounds_15_296 : exactInterval 15 296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_296 : oddCount 296 15 = 6 ∧ acceleratedOrbit 15 296 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 296) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_296.1, data_15_296.2]

/-- Complete interval computation for depth 15, residue 297. -/
theorem bounds_15_297 : exactInterval 15 297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_297 : oddCount 297 15 = 11 ∧ acceleratedOrbit 15 297 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 297) = 3 ^ 11 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_297.1, data_15_297.2]

/-- Complete interval computation for depth 15, residue 298. -/
theorem bounds_15_298 : exactInterval 15 298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_298 : oddCount 298 15 = 6 ∧ acceleratedOrbit 15 298 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 298) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_298.1, data_15_298.2]

/-- Complete interval computation for depth 15, residue 299. -/
theorem bounds_15_299 : exactInterval 15 299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_299 : oddCount 299 15 = 9 ∧ acceleratedOrbit 15 299 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 299) = 3 ^ 9 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_299.1, data_15_299.2]

/-- Complete interval computation for depth 15, residue 300. -/
theorem bounds_15_300 : exactInterval 15 300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_300 : oddCount 300 15 = 4 ∧ acceleratedOrbit 15 300 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 300) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_300.1, data_15_300.2]

/-- Complete interval computation for depth 15, residue 301. -/
theorem bounds_15_301 : exactInterval 15 301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_301 : oddCount 301 15 = 4 ∧ acceleratedOrbit 15 301 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 301) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_301.1, data_15_301.2]

/-- Complete interval computation for depth 15, residue 302. -/
theorem bounds_15_302 : exactInterval 15 302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_302 : oddCount 302 15 = 4 ∧ acceleratedOrbit 15 302 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 302) = 3 ^ 4 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_302.1, data_15_302.2]

/-- Complete interval computation for depth 15, residue 303. -/
theorem bounds_15_303 : exactInterval 15 303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_303 : oddCount 303 15 = 8 ∧ acceleratedOrbit 15 303 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 303) = 3 ^ 8 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_303.1, data_15_303.2]

/-- Complete interval computation for depth 15, residue 304. -/
theorem bounds_15_304 : exactInterval 15 304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_304 : oddCount 304 15 = 6 ∧ acceleratedOrbit 15 304 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 304) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_304.1, data_15_304.2]

/-- Complete interval computation for depth 15, residue 305. -/
theorem bounds_15_305 : exactInterval 15 305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_305 : oddCount 305 15 = 6 ∧ acceleratedOrbit 15 305 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 305) = 3 ^ 6 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_305.1, data_15_305.2]

/-- Complete interval computation for depth 15, residue 306. -/
theorem bounds_15_306 : exactInterval 15 306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_306 : oddCount 306 15 = 6 ∧ acceleratedOrbit 15 306 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 306) = 3 ^ 6 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_306.1, data_15_306.2]

/-- Complete interval computation for depth 15, residue 307. -/
theorem bounds_15_307 : exactInterval 15 307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_307 : oddCount 307 15 = 6 ∧ acceleratedOrbit 15 307 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 307) = 3 ^ 6 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_307.1, data_15_307.2]

/-- Complete interval computation for depth 15, residue 308. -/
theorem bounds_15_308 : exactInterval 15 308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_308 : oddCount 308 15 = 6 ∧ acceleratedOrbit 15 308 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 308) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_308.1, data_15_308.2]

/-- Complete interval computation for depth 15, residue 309. -/
theorem bounds_15_309 : exactInterval 15 309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_309 : oddCount 309 15 = 6 ∧ acceleratedOrbit 15 309 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 309) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_309.1, data_15_309.2]

/-- Complete interval computation for depth 15, residue 310. -/
theorem bounds_15_310 : exactInterval 15 310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_310 : oddCount 310 15 = 10 ∧ acceleratedOrbit 15 310 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 310) = 3 ^ 10 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_310.1, data_15_310.2]

/-- Complete interval computation for depth 15, residue 311. -/
theorem bounds_15_311 : exactInterval 15 311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_311 : oddCount 311 15 = 10 ∧ acceleratedOrbit 15 311 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 311) = 3 ^ 10 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_311.1, data_15_311.2]

/-- Complete interval computation for depth 15, residue 312. -/
theorem bounds_15_312 : exactInterval 15 312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_312 : oddCount 312 15 = 7 ∧ acceleratedOrbit 15 312 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 312) = 3 ^ 7 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_312.1, data_15_312.2]

/-- Complete interval computation for depth 15, residue 313. -/
theorem bounds_15_313 : exactInterval 15 313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_313 : oddCount 313 15 = 9 ∧ acceleratedOrbit 15 313 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 313) = 3 ^ 9 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_313.1, data_15_313.2]

/-- Complete interval computation for depth 15, residue 314. -/
theorem bounds_15_314 : exactInterval 15 314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_314 : oddCount 314 15 = 7 ∧ acceleratedOrbit 15 314 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 314) = 3 ^ 7 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_314.1, data_15_314.2]

/-- Complete interval computation for depth 15, residue 315. -/
theorem bounds_15_315 : exactInterval 15 315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_315 : oddCount 315 15 = 7 ∧ acceleratedOrbit 15 315 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 315) = 3 ^ 7 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_315.1, data_15_315.2]

/-- Complete interval computation for depth 15, residue 316. -/
theorem bounds_15_316 : exactInterval 15 316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_316 : oddCount 316 15 = 7 ∧ acceleratedOrbit 15 316 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 316) = 3 ^ 7 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_316.1, data_15_316.2]

/-- Complete interval computation for depth 15, residue 317. -/
theorem bounds_15_317 : exactInterval 15 317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_317 : oddCount 317 15 = 7 ∧ acceleratedOrbit 15 317 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 317) = 3 ^ 7 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_317.1, data_15_317.2]

/-- Complete interval computation for depth 15, residue 318. -/
theorem bounds_15_318 : exactInterval 15 318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_318 : oddCount 318 15 = 10 ∧ acceleratedOrbit 15 318 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 318) = 3 ^ 10 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_318.1, data_15_318.2]

/-- Complete interval computation for depth 15, residue 319. -/
theorem bounds_15_319 : exactInterval 15 319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_319 : oddCount 319 15 = 10 ∧ acceleratedOrbit 15 319 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 319) = 3 ^ 10 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_319.1, data_15_319.2]

/-- Complete interval computation for depth 15, residue 320. -/
theorem bounds_15_320 : exactInterval 15 320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_320 : oddCount 320 15 = 4 ∧ acceleratedOrbit 15 320 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 320) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_320.1, data_15_320.2]

/-- Complete interval computation for depth 15, residue 321. -/
theorem bounds_15_321 : exactInterval 15 321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_321 : oddCount 321 15 = 6 ∧ acceleratedOrbit 15 321 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 321) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_321.1, data_15_321.2]

/-- Complete interval computation for depth 15, residue 322. -/
theorem bounds_15_322 : exactInterval 15 322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_322 : oddCount 322 15 = 10 ∧ acceleratedOrbit 15 322 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 322) = 3 ^ 10 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_322.1, data_15_322.2]

/-- Complete interval computation for depth 15, residue 323. -/
theorem bounds_15_323 : exactInterval 15 323 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_323 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 323) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_323 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_323 : oddCount 323 15 = 10 ∧ acceleratedOrbit 15 323 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_323 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 323) = 3 ^ 10 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_323.1, data_15_323.2]

/-- Complete interval computation for depth 15, residue 324. -/
theorem bounds_15_324 : exactInterval 15 324 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_324 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 324) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_324 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_324 : oddCount 324 15 = 6 ∧ acceleratedOrbit 15 324 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_324 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 324) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_324.1, data_15_324.2]

/-- Complete interval computation for depth 15, residue 325. -/
theorem bounds_15_325 : exactInterval 15 325 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_325 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 325) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_325 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_325 : oddCount 325 15 = 6 ∧ acceleratedOrbit 15 325 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_325 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 325) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_325.1, data_15_325.2]

/-- Complete interval computation for depth 15, residue 326. -/
theorem bounds_15_326 : exactInterval 15 326 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_326 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 326) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_326 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_326 : oddCount 326 15 = 6 ∧ acceleratedOrbit 15 326 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_326 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 326) = 3 ^ 6 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_326.1, data_15_326.2]

end Collatz.Research.PassageAtlas.Batch0010
