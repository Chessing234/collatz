import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0376

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 12288. -/
theorem bounds_15_12288 : exactInterval 15 12288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12288 : oddCount 12288 15 = 2 ∧ acceleratedOrbit 15 12288 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12288) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12288.1, data_15_12288.2]

/-- Complete interval computation for depth 15, residue 12289. -/
theorem bounds_15_12289 : exactInterval 15 12289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12289 : oddCount 12289 15 = 7 ∧ acceleratedOrbit 15 12289 = 821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12289) = 3 ^ 7 * m + 821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12289.1, data_15_12289.2]

/-- Complete interval computation for depth 15, residue 12290. -/
theorem bounds_15_12290 : exactInterval 15 12290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12290 : oddCount 12290 15 = 7 ∧ acceleratedOrbit 15 12290 = 821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12290) = 3 ^ 7 * m + 821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12290.1, data_15_12290.2]

/-- Complete interval computation for depth 15, residue 12291. -/
theorem bounds_15_12291 : exactInterval 15 12291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12291 : oddCount 12291 15 = 7 ∧ acceleratedOrbit 15 12291 = 821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12291) = 3 ^ 7 * m + 821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12291.1, data_15_12291.2]

/-- Complete interval computation for depth 15, residue 12292. -/
theorem bounds_15_12292 : exactInterval 15 12292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12292 : oddCount 12292 15 = 6 ∧ acceleratedOrbit 15 12292 = 274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12292) = 3 ^ 6 * m + 274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12292.1, data_15_12292.2]

/-- Complete interval computation for depth 15, residue 12293. -/
theorem bounds_15_12293 : exactInterval 15 12293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12293 : oddCount 12293 15 = 6 ∧ acceleratedOrbit 15 12293 = 274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12293) = 3 ^ 6 * m + 274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12293.1, data_15_12293.2]

/-- Complete interval computation for depth 15, residue 12294. -/
theorem bounds_15_12294 : exactInterval 15 12294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12294 : oddCount 12294 15 = 6 ∧ acceleratedOrbit 15 12294 = 274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12294) = 3 ^ 6 * m + 274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12294.1, data_15_12294.2]

/-- Complete interval computation for depth 15, residue 12295. -/
theorem bounds_15_12295 : exactInterval 15 12295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12295 : oddCount 12295 15 = 7 ∧ acceleratedOrbit 15 12295 = 821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12295) = 3 ^ 7 * m + 821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12295.1, data_15_12295.2]

/-- Complete interval computation for depth 15, residue 12296. -/
theorem bounds_15_12296 : exactInterval 15 12296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12296 : oddCount 12296 15 = 7 ∧ acceleratedOrbit 15 12296 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12296) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12296.1, data_15_12296.2]

/-- Complete interval computation for depth 15, residue 12297. -/
theorem bounds_15_12297 : exactInterval 15 12297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12297 : oddCount 12297 15 = 7 ∧ acceleratedOrbit 15 12297 = 821 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12297) = 3 ^ 7 * m + 821 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12297.1, data_15_12297.2]

/-- Complete interval computation for depth 15, residue 12298. -/
theorem bounds_15_12298 : exactInterval 15 12298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12298 : oddCount 12298 15 = 7 ∧ acceleratedOrbit 15 12298 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12298) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12298.1, data_15_12298.2]

/-- Complete interval computation for depth 15, residue 12299. -/
theorem bounds_15_12299 : exactInterval 15 12299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12299 : oddCount 12299 15 = 6 ∧ acceleratedOrbit 15 12299 = 274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12299) = 3 ^ 6 * m + 274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12299.1, data_15_12299.2]

/-- Complete interval computation for depth 15, residue 12300. -/
theorem bounds_15_12300 : exactInterval 15 12300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12300 : oddCount 12300 15 = 7 ∧ acceleratedOrbit 15 12300 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12300) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12300.1, data_15_12300.2]

/-- Complete interval computation for depth 15, residue 12301. -/
theorem bounds_15_12301 : exactInterval 15 12301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12301 : oddCount 12301 15 = 7 ∧ acceleratedOrbit 15 12301 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12301) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12301.1, data_15_12301.2]

/-- Complete interval computation for depth 15, residue 12302. -/
theorem bounds_15_12302 : exactInterval 15 12302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12302 : oddCount 12302 15 = 6 ∧ acceleratedOrbit 15 12302 = 274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12302) = 3 ^ 6 * m + 274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12302.1, data_15_12302.2]

/-- Complete interval computation for depth 15, residue 12303. -/
theorem bounds_15_12303 : exactInterval 15 12303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12303 : oddCount 12303 15 = 6 ∧ acceleratedOrbit 15 12303 = 274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12303) = 3 ^ 6 * m + 274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12303.1, data_15_12303.2]

/-- Complete interval computation for depth 15, residue 12304. -/
theorem bounds_15_12304 : exactInterval 15 12304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12304 : oddCount 12304 15 = 5 ∧ acceleratedOrbit 15 12304 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12304) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12304.1, data_15_12304.2]

/-- Complete interval computation for depth 15, residue 12305. -/
theorem bounds_15_12305 : exactInterval 15 12305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12305 : oddCount 12305 15 = 7 ∧ acceleratedOrbit 15 12305 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12305) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12305.1, data_15_12305.2]

/-- Complete interval computation for depth 15, residue 12306. -/
theorem bounds_15_12306 : exactInterval 15 12306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12306 : oddCount 12306 15 = 9 ∧ acceleratedOrbit 15 12306 = 7397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12306) = 3 ^ 9 * m + 7397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12306.1, data_15_12306.2]

/-- Complete interval computation for depth 15, residue 12307. -/
theorem bounds_15_12307 : exactInterval 15 12307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12307 : oddCount 12307 15 = 9 ∧ acceleratedOrbit 15 12307 = 7397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12307) = 3 ^ 9 * m + 7397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12307.1, data_15_12307.2]

/-- Complete interval computation for depth 15, residue 12308. -/
theorem bounds_15_12308 : exactInterval 15 12308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12308 : oddCount 12308 15 = 5 ∧ acceleratedOrbit 15 12308 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12308) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12308.1, data_15_12308.2]

/-- Complete interval computation for depth 15, residue 12309. -/
theorem bounds_15_12309 : exactInterval 15 12309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12309 : oddCount 12309 15 = 5 ∧ acceleratedOrbit 15 12309 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12309) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12309.1, data_15_12309.2]

/-- Complete interval computation for depth 15, residue 12310. -/
theorem bounds_15_12310 : exactInterval 15 12310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12310 : oddCount 12310 15 = 7 ∧ acceleratedOrbit 15 12310 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12310) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12310.1, data_15_12310.2]

/-- Complete interval computation for depth 15, residue 12311. -/
theorem bounds_15_12311 : exactInterval 15 12311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12311 : oddCount 12311 15 = 7 ∧ acceleratedOrbit 15 12311 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12311) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12311.1, data_15_12311.2]

/-- Complete interval computation for depth 15, residue 12312. -/
theorem bounds_15_12312 : exactInterval 15 12312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12312 : oddCount 12312 15 = 5 ∧ acceleratedOrbit 15 12312 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12312) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12312.1, data_15_12312.2]

/-- Complete interval computation for depth 15, residue 12313. -/
theorem bounds_15_12313 : exactInterval 15 12313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12313 : oddCount 12313 15 = 6 ∧ acceleratedOrbit 15 12313 = 274 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12313) = 3 ^ 6 * m + 274 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12313.1, data_15_12313.2]

/-- Complete interval computation for depth 15, residue 12314. -/
theorem bounds_15_12314 : exactInterval 15 12314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12314 : oddCount 12314 15 = 5 ∧ acceleratedOrbit 15 12314 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12314) = 3 ^ 5 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12314.1, data_15_12314.2]

/-- Complete interval computation for depth 15, residue 12315. -/
theorem bounds_15_12315 : exactInterval 15 12315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12315 : oddCount 12315 15 = 10 ∧ acceleratedOrbit 15 12315 = 22195 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12315) = 3 ^ 10 * m + 22195 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12315.1, data_15_12315.2]

/-- Complete interval computation for depth 15, residue 12316. -/
theorem bounds_15_12316 : exactInterval 15 12316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12316 : oddCount 12316 15 = 7 ∧ acceleratedOrbit 15 12316 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12316) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12316.1, data_15_12316.2]

/-- Complete interval computation for depth 15, residue 12317. -/
theorem bounds_15_12317 : exactInterval 15 12317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12317 : oddCount 12317 15 = 7 ∧ acceleratedOrbit 15 12317 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12317) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12317.1, data_15_12317.2]

/-- Complete interval computation for depth 15, residue 12318. -/
theorem bounds_15_12318 : exactInterval 15 12318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12318 : oddCount 12318 15 = 7 ∧ acceleratedOrbit 15 12318 = 823 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12318) = 3 ^ 7 * m + 823 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12318.1, data_15_12318.2]

/-- Complete interval computation for depth 15, residue 12319. -/
theorem bounds_15_12319 : exactInterval 15 12319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_12319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 12319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_12319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_12319 : oddCount 12319 15 = 10 ∧ acceleratedOrbit 15 12319 = 22202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_12319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 12319) = 3 ^ 10 * m + 22202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_12319.1, data_15_12319.2]

end Collatz.Research.PassageAtlas.Batch0376
