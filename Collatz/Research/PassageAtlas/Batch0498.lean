import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0498

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 16285. -/
theorem bounds_15_16285 : exactInterval 15 16285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16285 : oddCount 16285 15 = 8 ∧ acceleratedOrbit 15 16285 = 3262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16285) = 3 ^ 8 * m + 3262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16285.1, data_15_16285.2]

/-- Complete interval computation for depth 15, residue 16286. -/
theorem bounds_15_16286 : exactInterval 15 16286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16286 : oddCount 16286 15 = 8 ∧ acceleratedOrbit 15 16286 = 3262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16286) = 3 ^ 8 * m + 3262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16286.1, data_15_16286.2]

/-- Complete interval computation for depth 15, residue 16287. -/
theorem bounds_15_16287 : exactInterval 15 16287 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16287) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16287 : oddCount 16287 15 = 9 ∧ acceleratedOrbit 15 16287 = 9784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16287) = 3 ^ 9 * m + 9784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16287.1, data_15_16287.2]

/-- Complete interval computation for depth 15, residue 16288. -/
theorem bounds_15_16288 : exactInterval 15 16288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16288 : oddCount 16288 15 = 7 ∧ acceleratedOrbit 15 16288 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16288) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16288.1, data_15_16288.2]

/-- Complete interval computation for depth 15, residue 16289. -/
theorem bounds_15_16289 : exactInterval 15 16289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16289 : oddCount 16289 15 = 7 ∧ acceleratedOrbit 15 16289 = 1088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16289) = 3 ^ 7 * m + 1088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16289.1, data_15_16289.2]

/-- Complete interval computation for depth 15, residue 16290. -/
theorem bounds_15_16290 : exactInterval 15 16290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16290 : oddCount 16290 15 = 8 ∧ acceleratedOrbit 15 16290 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16290) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16290.1, data_15_16290.2]

/-- Complete interval computation for depth 15, residue 16291. -/
theorem bounds_15_16291 : exactInterval 15 16291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16291 : oddCount 16291 15 = 8 ∧ acceleratedOrbit 15 16291 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16291) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16291.1, data_15_16291.2]

/-- Complete interval computation for depth 15, residue 16292. -/
theorem bounds_15_16292 : exactInterval 15 16292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16292 : oddCount 16292 15 = 9 ∧ acceleratedOrbit 15 16292 = 9791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16292) = 3 ^ 9 * m + 9791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16292.1, data_15_16292.2]

/-- Complete interval computation for depth 15, residue 16293. -/
theorem bounds_15_16293 : exactInterval 15 16293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16293 : oddCount 16293 15 = 9 ∧ acceleratedOrbit 15 16293 = 9791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16293) = 3 ^ 9 * m + 9791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16293.1, data_15_16293.2]

/-- Complete interval computation for depth 15, residue 16294. -/
theorem bounds_15_16294 : exactInterval 15 16294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16294 : oddCount 16294 15 = 9 ∧ acceleratedOrbit 15 16294 = 9791 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16294) = 3 ^ 9 * m + 9791 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16294.1, data_15_16294.2]

/-- Complete interval computation for depth 15, residue 16295. -/
theorem bounds_15_16295 : exactInterval 15 16295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16295 : oddCount 16295 15 = 8 ∧ acceleratedOrbit 15 16295 = 3263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16295) = 3 ^ 8 * m + 3263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16295.1, data_15_16295.2]

/-- Complete interval computation for depth 15, residue 16296. -/
theorem bounds_15_16296 : exactInterval 15 16296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16296 : oddCount 16296 15 = 7 ∧ acceleratedOrbit 15 16296 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16296) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16296.1, data_15_16296.2]

/-- Complete interval computation for depth 15, residue 16297. -/
theorem bounds_15_16297 : exactInterval 15 16297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16297 : oddCount 16297 15 = 10 ∧ acceleratedOrbit 15 16297 = 29371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16297) = 3 ^ 10 * m + 29371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16297.1, data_15_16297.2]

/-- Complete interval computation for depth 15, residue 16298. -/
theorem bounds_15_16298 : exactInterval 15 16298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16298 : oddCount 16298 15 = 7 ∧ acceleratedOrbit 15 16298 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16298) = 3 ^ 7 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16298.1, data_15_16298.2]

/-- Complete interval computation for depth 15, residue 16299. -/
theorem bounds_15_16299 : exactInterval 15 16299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16299 : oddCount 16299 15 = 7 ∧ acceleratedOrbit 15 16299 = 1088 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16299) = 3 ^ 7 * m + 1088 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16299.1, data_15_16299.2]

/-- Complete interval computation for depth 15, residue 16300. -/
theorem bounds_15_16300 : exactInterval 15 16300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16300 : oddCount 16300 15 = 9 ∧ acceleratedOrbit 15 16300 = 9796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16300) = 3 ^ 9 * m + 9796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16300.1, data_15_16300.2]

/-- Complete interval computation for depth 15, residue 16301. -/
theorem bounds_15_16301 : exactInterval 15 16301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16301 : oddCount 16301 15 = 9 ∧ acceleratedOrbit 15 16301 = 9796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16301) = 3 ^ 9 * m + 9796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16301.1, data_15_16301.2]

/-- Complete interval computation for depth 15, residue 16302. -/
theorem bounds_15_16302 : exactInterval 15 16302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16302 : oddCount 16302 15 = 9 ∧ acceleratedOrbit 15 16302 = 9796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16302) = 3 ^ 9 * m + 9796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16302.1, data_15_16302.2]

/-- Complete interval computation for depth 15, residue 16303. -/
theorem bounds_15_16303 : exactInterval 15 16303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16303 : oddCount 16303 15 = 8 ∧ acceleratedOrbit 15 16303 = 3266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16303) = 3 ^ 8 * m + 3266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16303.1, data_15_16303.2]

/-- Complete interval computation for depth 15, residue 16304. -/
theorem bounds_15_16304 : exactInterval 15 16304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16304 : oddCount 16304 15 = 7 ∧ acceleratedOrbit 15 16304 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16304) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16304.1, data_15_16304.2]

/-- Complete interval computation for depth 15, residue 16305. -/
theorem bounds_15_16305 : exactInterval 15 16305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16305 : oddCount 16305 15 = 6 ∧ acceleratedOrbit 15 16305 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16305) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16305.1, data_15_16305.2]

/-- Complete interval computation for depth 15, residue 16306. -/
theorem bounds_15_16306 : exactInterval 15 16306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16306 : oddCount 16306 15 = 6 ∧ acceleratedOrbit 15 16306 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16306) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16306.1, data_15_16306.2]

/-- Complete interval computation for depth 15, residue 16307. -/
theorem bounds_15_16307 : exactInterval 15 16307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16307 : oddCount 16307 15 = 6 ∧ acceleratedOrbit 15 16307 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16307) = 3 ^ 6 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16307.1, data_15_16307.2]

/-- Complete interval computation for depth 15, residue 16308. -/
theorem bounds_15_16308 : exactInterval 15 16308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16308 : oddCount 16308 15 = 7 ∧ acceleratedOrbit 15 16308 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16308) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16308.1, data_15_16308.2]

/-- Complete interval computation for depth 15, residue 16309. -/
theorem bounds_15_16309 : exactInterval 15 16309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16309 : oddCount 16309 15 = 7 ∧ acceleratedOrbit 15 16309 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16309) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16309.1, data_15_16309.2]

/-- Complete interval computation for depth 15, residue 16310. -/
theorem bounds_15_16310 : exactInterval 15 16310 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16310 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16310) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16310 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16310 : oddCount 16310 15 = 10 ∧ acceleratedOrbit 15 16310 = 29402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16310 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16310) = 3 ^ 10 * m + 29402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16310.1, data_15_16310.2]

/-- Complete interval computation for depth 15, residue 16311. -/
theorem bounds_15_16311 : exactInterval 15 16311 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16311 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16311) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16311 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16311 : oddCount 16311 15 = 10 ∧ acceleratedOrbit 15 16311 = 29402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16311 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16311) = 3 ^ 10 * m + 29402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16311.1, data_15_16311.2]

/-- Complete interval computation for depth 15, residue 16312. -/
theorem bounds_15_16312 : exactInterval 15 16312 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16312 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16312) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16312 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16312 : oddCount 16312 15 = 7 ∧ acceleratedOrbit 15 16312 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16312 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16312) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16312.1, data_15_16312.2]

/-- Complete interval computation for depth 15, residue 16313. -/
theorem bounds_15_16313 : exactInterval 15 16313 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16313 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16313) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16313 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16313 : oddCount 16313 15 = 5 ∧ acceleratedOrbit 15 16313 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16313 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16313) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16313.1, data_15_16313.2]

/-- Complete interval computation for depth 15, residue 16314. -/
theorem bounds_15_16314 : exactInterval 15 16314 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16314 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16314) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16314 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16314 : oddCount 16314 15 = 7 ∧ acceleratedOrbit 15 16314 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16314 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16314) = 3 ^ 7 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16314.1, data_15_16314.2]

/-- Complete interval computation for depth 15, residue 16315. -/
theorem bounds_15_16315 : exactInterval 15 16315 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16315 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16315) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16315 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16315 : oddCount 16315 15 = 5 ∧ acceleratedOrbit 15 16315 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16315 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16315) = 3 ^ 5 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16315.1, data_15_16315.2]

/-- Complete interval computation for depth 15, residue 16316. -/
theorem bounds_15_16316 : exactInterval 15 16316 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16316 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16316) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16316 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16316 : oddCount 16316 15 = 8 ∧ acceleratedOrbit 15 16316 = 3268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16316 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16316) = 3 ^ 8 * m + 3268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16316.1, data_15_16316.2]

/-- Complete interval computation for depth 15, residue 16317. -/
theorem bounds_15_16317 : exactInterval 15 16317 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_16317 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 16317) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_16317 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_16317 : oddCount 16317 15 = 8 ∧ acceleratedOrbit 15 16317 = 3268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_16317 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 16317) = 3 ^ 8 * m + 3268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_16317.1, data_15_16317.2]

end Collatz.Research.PassageAtlas.Batch0498
