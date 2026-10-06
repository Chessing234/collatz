import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0254

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8290. -/
theorem bounds_15_8290 : exactInterval 15 8290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8290 : oddCount 8290 15 = 8 ∧ acceleratedOrbit 15 8290 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8290) = 3 ^ 8 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8290.1, data_15_8290.2]

/-- Complete interval computation for depth 15, residue 8291. -/
theorem bounds_15_8291 : exactInterval 15 8291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8291 : oddCount 8291 15 = 8 ∧ acceleratedOrbit 15 8291 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8291) = 3 ^ 8 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8291.1, data_15_8291.2]

/-- Complete interval computation for depth 15, residue 8292. -/
theorem bounds_15_8292 : exactInterval 15 8292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8292 : oddCount 8292 15 = 8 ∧ acceleratedOrbit 15 8292 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8292) = 3 ^ 8 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8292.1, data_15_8292.2]

/-- Complete interval computation for depth 15, residue 8293. -/
theorem bounds_15_8293 : exactInterval 15 8293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8293 : oddCount 8293 15 = 8 ∧ acceleratedOrbit 15 8293 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8293) = 3 ^ 8 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8293.1, data_15_8293.2]

/-- Complete interval computation for depth 15, residue 8294. -/
theorem bounds_15_8294 : exactInterval 15 8294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8294 : oddCount 8294 15 = 8 ∧ acceleratedOrbit 15 8294 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8294) = 3 ^ 8 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8294.1, data_15_8294.2]

/-- Complete interval computation for depth 15, residue 8295. -/
theorem bounds_15_8295 : exactInterval 15 8295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8295 : oddCount 8295 15 = 10 ∧ acceleratedOrbit 15 8295 = 14951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8295) = 3 ^ 10 * m + 14951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8295.1, data_15_8295.2]

/-- Complete interval computation for depth 15, residue 8296. -/
theorem bounds_15_8296 : exactInterval 15 8296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8296 : oddCount 8296 15 = 6 ∧ acceleratedOrbit 15 8296 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8296) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8296.1, data_15_8296.2]

/-- Complete interval computation for depth 15, residue 8297. -/
theorem bounds_15_8297 : exactInterval 15 8297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8297 : oddCount 8297 15 = 7 ∧ acceleratedOrbit 15 8297 = 554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8297) = 3 ^ 7 * m + 554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8297.1, data_15_8297.2]

/-- Complete interval computation for depth 15, residue 8298. -/
theorem bounds_15_8298 : exactInterval 15 8298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8298 : oddCount 8298 15 = 6 ∧ acceleratedOrbit 15 8298 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8298) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8298.1, data_15_8298.2]

/-- Complete interval computation for depth 15, residue 8299. -/
theorem bounds_15_8299 : exactInterval 15 8299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8299 : oddCount 8299 15 = 10 ∧ acceleratedOrbit 15 8299 = 14960 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8299) = 3 ^ 10 * m + 14960 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8299.1, data_15_8299.2]

/-- Complete interval computation for depth 15, residue 8300. -/
theorem bounds_15_8300 : exactInterval 15 8300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8300 : oddCount 8300 15 = 8 ∧ acceleratedOrbit 15 8300 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8300) = 3 ^ 8 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8300.1, data_15_8300.2]

/-- Complete interval computation for depth 15, residue 8301. -/
theorem bounds_15_8301 : exactInterval 15 8301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8301 : oddCount 8301 15 = 8 ∧ acceleratedOrbit 15 8301 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8301) = 3 ^ 8 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8301.1, data_15_8301.2]

/-- Complete interval computation for depth 15, residue 8302. -/
theorem bounds_15_8302 : exactInterval 15 8302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8302 : oddCount 8302 15 = 8 ∧ acceleratedOrbit 15 8302 = 1663 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8302) = 3 ^ 8 * m + 1663 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8302.1, data_15_8302.2]

/-- Complete interval computation for depth 15, residue 8303. -/
theorem bounds_15_8303 : exactInterval 15 8303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8303 : oddCount 8303 15 = 11 ∧ acceleratedOrbit 15 8303 = 44894 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8303) = 3 ^ 11 * m + 44894 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8303.1, data_15_8303.2]

/-- Complete interval computation for depth 15, residue 8304. -/
theorem bounds_15_8304 : exactInterval 15 8304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8304 : oddCount 8304 15 = 7 ∧ acceleratedOrbit 15 8304 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8304) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8304.1, data_15_8304.2]

/-- Complete interval computation for depth 15, residue 8305. -/
theorem bounds_15_8305 : exactInterval 15 8305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8305 : oddCount 8305 15 = 6 ∧ acceleratedOrbit 15 8305 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8305) = 3 ^ 6 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8305.1, data_15_8305.2]

/-- Complete interval computation for depth 15, residue 8306. -/
theorem bounds_15_8306 : exactInterval 15 8306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8306 : oddCount 8306 15 = 6 ∧ acceleratedOrbit 15 8306 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8306) = 3 ^ 6 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8306.1, data_15_8306.2]

/-- Complete interval computation for depth 15, residue 8307. -/
theorem bounds_15_8307 : exactInterval 15 8307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8307 : oddCount 8307 15 = 6 ∧ acceleratedOrbit 15 8307 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8307) = 3 ^ 6 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8307.1, data_15_8307.2]

/-- Complete interval computation for depth 15, residue 8308. -/
theorem bounds_15_8308 : exactInterval 15 8308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8308 : oddCount 8308 15 = 7 ∧ acceleratedOrbit 15 8308 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8308) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8308.1, data_15_8308.2]

/-- Complete interval computation for depth 15, residue 8309. -/
theorem bounds_15_8309 : exactInterval 15 8309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8309 : oddCount 8309 15 = 7 ∧ acceleratedOrbit 15 8309 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8309) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8309.1, data_15_8309.2]

/-- Complete interval computation for depth 15, residue 8310. -/
theorem bounds_15_8310 : exactInterval 15 8310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8310 : oddCount 8310 15 = 6 ∧ acceleratedOrbit 15 8310 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8310) = 3 ^ 6 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8310.1, data_15_8310.2]

/-- Complete interval computation for depth 15, residue 8311. -/
theorem bounds_15_8311 : exactInterval 15 8311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8311 : oddCount 8311 15 = 6 ∧ acceleratedOrbit 15 8311 = 185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8311) = 3 ^ 6 * m + 185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8311.1, data_15_8311.2]

/-- Complete interval computation for depth 15, residue 8312. -/
theorem bounds_15_8312 : exactInterval 15 8312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8312 : oddCount 8312 15 = 7 ∧ acceleratedOrbit 15 8312 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8312) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8312.1, data_15_8312.2]

/-- Complete interval computation for depth 15, residue 8313. -/
theorem bounds_15_8313 : exactInterval 15 8313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8313 : oddCount 8313 15 = 12 ∧ acceleratedOrbit 15 8313 = 134864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8313) = 3 ^ 12 * m + 134864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8313.1, data_15_8313.2]

/-- Complete interval computation for depth 15, residue 8314. -/
theorem bounds_15_8314 : exactInterval 15 8314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8314 : oddCount 8314 15 = 7 ∧ acceleratedOrbit 15 8314 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8314) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8314.1, data_15_8314.2]

/-- Complete interval computation for depth 15, residue 8315. -/
theorem bounds_15_8315 : exactInterval 15 8315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8315 : oddCount 8315 15 = 9 ∧ acceleratedOrbit 15 8315 = 4997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8315) = 3 ^ 9 * m + 4997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8315.1, data_15_8315.2]

/-- Complete interval computation for depth 15, residue 8316. -/
theorem bounds_15_8316 : exactInterval 15 8316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8316 : oddCount 8316 15 = 8 ∧ acceleratedOrbit 15 8316 = 1666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8316) = 3 ^ 8 * m + 1666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8316.1, data_15_8316.2]

/-- Complete interval computation for depth 15, residue 8317. -/
theorem bounds_15_8317 : exactInterval 15 8317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8317 : oddCount 8317 15 = 8 ∧ acceleratedOrbit 15 8317 = 1666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8317) = 3 ^ 8 * m + 1666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8317.1, data_15_8317.2]

/-- Complete interval computation for depth 15, residue 8318. -/
theorem bounds_15_8318 : exactInterval 15 8318 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8318 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8318) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8318 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8318 : oddCount 8318 15 = 8 ∧ acceleratedOrbit 15 8318 = 1666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8318 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8318) = 3 ^ 8 * m + 1666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8318.1, data_15_8318.2]

/-- Complete interval computation for depth 15, residue 8319. -/
theorem bounds_15_8319 : exactInterval 15 8319 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8319 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8319) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8319 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8319 : oddCount 8319 15 = 11 ∧ acceleratedOrbit 15 8319 = 44981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8319 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8319) = 3 ^ 11 * m + 44981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8319.1, data_15_8319.2]

/-- Complete interval computation for depth 15, residue 8320. -/
theorem bounds_15_8320 : exactInterval 15 8320 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8320 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8320) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8320 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8320 : oddCount 8320 15 = 3 ∧ acceleratedOrbit 15 8320 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8320 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8320) = 3 ^ 3 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8320.1, data_15_8320.2]

/-- Complete interval computation for depth 15, residue 8321. -/
theorem bounds_15_8321 : exactInterval 15 8321 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8321 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8321) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8321 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8321 : oddCount 8321 15 = 8 ∧ acceleratedOrbit 15 8321 = 1667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8321 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8321) = 3 ^ 8 * m + 1667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8321.1, data_15_8321.2]

/-- Complete interval computation for depth 15, residue 8322. -/
theorem bounds_15_8322 : exactInterval 15 8322 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8322 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8322) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8322 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8322 : oddCount 8322 15 = 7 ∧ acceleratedOrbit 15 8322 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8322 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8322) = 3 ^ 7 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8322.1, data_15_8322.2]

end Collatz.Research.PassageAtlas.Batch0254
