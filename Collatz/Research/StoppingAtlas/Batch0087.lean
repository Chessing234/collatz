import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0087

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 296. -/
theorem bounds_11_296 : exactInterval 11 296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_296 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 296) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_296 : oddCount 296 11 = 4 ∧ acceleratedOrbit 11 296 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_296 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 296) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_296.1, data_11_296.2]

/-- Complete interval computation for depth 11, residue 297. -/
theorem bounds_11_297 : exactInterval 11 297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_297 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 297) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_297 : oddCount 297 11 = 7 ∧ acceleratedOrbit 11 297 = 319 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_297 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 297) = 3 ^ 7 * m + 319 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_297.1, data_11_297.2]

/-- Complete interval computation for depth 11, residue 298. -/
theorem bounds_11_298 : exactInterval 11 298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_298 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 298) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_298 : oddCount 298 11 = 4 ∧ acceleratedOrbit 11 298 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_298 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 298) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_298.1, data_11_298.2]

/-- Complete interval computation for depth 11, residue 299. -/
theorem bounds_11_299 : exactInterval 11 299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_299 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 299) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_299 : oddCount 299 11 = 7 ∧ acceleratedOrbit 11 299 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_299 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 299) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_299.1, data_11_299.2]

/-- Complete interval computation for depth 11, residue 300. -/
theorem bounds_11_300 : exactInterval 11 300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_300 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 300) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_300 : oddCount 300 11 = 3 ∧ acceleratedOrbit 11 300 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_300 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 300) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_300.1, data_11_300.2]

/-- Complete interval computation for depth 11, residue 301. -/
theorem bounds_11_301 : exactInterval 11 301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_301 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 301) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_301 : oddCount 301 11 = 3 ∧ acceleratedOrbit 11 301 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_301 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 301) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_301.1, data_11_301.2]

/-- Complete interval computation for depth 11, residue 302. -/
theorem bounds_11_302 : exactInterval 11 302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_302 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 302) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_302 : oddCount 302 11 = 3 ∧ acceleratedOrbit 11 302 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_302 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 302) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_302.1, data_11_302.2]

/-- Complete interval computation for depth 11, residue 303. -/
theorem bounds_11_303 : exactInterval 11 303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_303 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 303) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_303 : oddCount 303 11 = 7 ∧ acceleratedOrbit 11 303 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_303 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 303) = 3 ^ 7 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_303.1, data_11_303.2]

/-- Complete interval computation for depth 11, residue 304. -/
theorem bounds_11_304 : exactInterval 11 304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_304 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 304) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_304 : oddCount 304 11 = 4 ∧ acceleratedOrbit 11 304 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_304 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 304) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_304.1, data_11_304.2]

/-- Complete interval computation for depth 11, residue 305. -/
theorem bounds_11_305 : exactInterval 11 305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_305 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 305) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_305 : oddCount 305 11 = 5 ∧ acceleratedOrbit 11 305 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_305 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 305) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_305.1, data_11_305.2]

/-- Complete interval computation for depth 11, residue 306. -/
theorem bounds_11_306 : exactInterval 11 306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_306 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 306) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_306 : oddCount 306 11 = 5 ∧ acceleratedOrbit 11 306 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_306 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 306) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_306.1, data_11_306.2]

/-- Complete interval computation for depth 11, residue 307. -/
theorem bounds_11_307 : exactInterval 11 307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_307 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 307) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_307 : oddCount 307 11 = 5 ∧ acceleratedOrbit 11 307 = 37 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_307 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 307) = 3 ^ 5 * m + 37 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_307.1, data_11_307.2]

/-- Complete interval computation for depth 11, residue 308. -/
theorem bounds_11_308 : exactInterval 11 308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_308 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 308) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_308 : oddCount 308 11 = 4 ∧ acceleratedOrbit 11 308 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_308 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 308) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_308.1, data_11_308.2]

/-- Complete interval computation for depth 11, residue 309. -/
theorem bounds_11_309 : exactInterval 11 309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_309 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 309) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_309 : oddCount 309 11 = 4 ∧ acceleratedOrbit 11 309 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_309 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 309) = 3 ^ 4 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_309.1, data_11_309.2]

/-- Complete interval computation for depth 11, residue 310. -/
theorem bounds_11_310 : exactInterval 11 310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_310 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 310) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_310 : oddCount 310 11 = 7 ∧ acceleratedOrbit 11 310 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_310 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 310) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_310.1, data_11_310.2]

/-- Complete interval computation for depth 11, residue 311. -/
theorem bounds_11_311 : exactInterval 11 311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_311 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 311) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_311 : oddCount 311 11 = 7 ∧ acceleratedOrbit 11 311 = 334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_311 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 311) = 3 ^ 7 * m + 334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_311.1, data_11_311.2]

end Collatz.Research.StoppingAtlas.Batch0087
