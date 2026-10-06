import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0487

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 296. -/
theorem bounds_13_296 : exactInterval 13 296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_296 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 296) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_296 : oddCount 296 13 = 5 ∧ acceleratedOrbit 13 296 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_296 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 296) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_296.1, data_13_296.2]

/-- Complete interval computation for depth 13, residue 297. -/
theorem bounds_13_297 : exactInterval 13 297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_297 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 297) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_297 : oddCount 297 13 = 9 ∧ acceleratedOrbit 13 297 = 719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_297 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 297) = 3 ^ 9 * m + 719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_297.1, data_13_297.2]

/-- Complete interval computation for depth 13, residue 298. -/
theorem bounds_13_298 : exactInterval 13 298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_298 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 298) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_298 : oddCount 298 13 = 5 ∧ acceleratedOrbit 13 298 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_298 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 298) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_298.1, data_13_298.2]

/-- Complete interval computation for depth 13, residue 299. -/
theorem bounds_13_299 : exactInterval 13 299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_299 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 299) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_299 : oddCount 299 13 = 9 ∧ acceleratedOrbit 13 299 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_299 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 299) = 3 ^ 9 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_299.1, data_13_299.2]

/-- Complete interval computation for depth 13, residue 300. -/
theorem bounds_13_300 : exactInterval 13 300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_300 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 300) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_300 : oddCount 300 13 = 3 ∧ acceleratedOrbit 13 300 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_300 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 300) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_300.1, data_13_300.2]

/-- Complete interval computation for depth 13, residue 301. -/
theorem bounds_13_301 : exactInterval 13 301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_301 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 301) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_301 : oddCount 301 13 = 3 ∧ acceleratedOrbit 13 301 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_301 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 301) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_301.1, data_13_301.2]

/-- Complete interval computation for depth 13, residue 302. -/
theorem bounds_13_302 : exactInterval 13 302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_302 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 302) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_302 : oddCount 302 13 = 3 ∧ acceleratedOrbit 13 302 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_302 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 302) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_302.1, data_13_302.2]

/-- Complete interval computation for depth 13, residue 303. -/
theorem bounds_13_303 : exactInterval 13 303 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_303 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 303) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_303 : oddCount 303 13 = 8 ∧ acceleratedOrbit 13 303 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_303 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 303) = 3 ^ 8 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_303.1, data_13_303.2]

/-- Complete interval computation for depth 13, residue 304. -/
theorem bounds_13_304 : exactInterval 13 304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_304 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 304) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_304 : oddCount 304 13 = 5 ∧ acceleratedOrbit 13 304 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_304 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 304) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_304.1, data_13_304.2]

/-- Complete interval computation for depth 13, residue 305. -/
theorem bounds_13_305 : exactInterval 13 305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_305 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 305) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_305 : oddCount 305 13 = 6 ∧ acceleratedOrbit 13 305 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_305 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 305) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_305.1, data_13_305.2]

/-- Complete interval computation for depth 13, residue 306. -/
theorem bounds_13_306 : exactInterval 13 306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_306 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 306) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_306 : oddCount 306 13 = 6 ∧ acceleratedOrbit 13 306 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_306 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 306) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_306.1, data_13_306.2]

/-- Complete interval computation for depth 13, residue 307. -/
theorem bounds_13_307 : exactInterval 13 307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_307 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 307) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_307 : oddCount 307 13 = 6 ∧ acceleratedOrbit 13 307 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_307 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 307) = 3 ^ 6 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_307.1, data_13_307.2]

/-- Complete interval computation for depth 13, residue 308. -/
theorem bounds_13_308 : exactInterval 13 308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_308 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 308) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_308 : oddCount 308 13 = 5 ∧ acceleratedOrbit 13 308 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_308 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 308) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_308.1, data_13_308.2]

/-- Complete interval computation for depth 13, residue 309. -/
theorem bounds_13_309 : exactInterval 13 309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_309 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 309) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_309 : oddCount 309 13 = 5 ∧ acceleratedOrbit 13 309 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_309 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 309) = 3 ^ 5 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_309.1, data_13_309.2]

/-- Complete interval computation for depth 13, residue 310. -/
theorem bounds_13_310 : exactInterval 13 310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_310 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 310) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_310 : oddCount 310 13 = 8 ∧ acceleratedOrbit 13 310 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_310 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 310) = 3 ^ 8 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_310.1, data_13_310.2]

/-- Complete interval computation for depth 13, residue 311. -/
theorem bounds_13_311 : exactInterval 13 311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_311 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 311) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_311 : oddCount 311 13 = 8 ∧ acceleratedOrbit 13 311 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_311 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 311) = 3 ^ 8 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_311.1, data_13_311.2]

end Collatz.Research.StoppingAtlas.Batch0487
