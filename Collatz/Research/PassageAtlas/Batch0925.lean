import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0925

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30277. -/
theorem bounds_15_30277 : exactInterval 15 30277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30277 : oddCount 30277 15 = 7 ∧ acceleratedOrbit 15 30277 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30277) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30277.1, data_15_30277.2]

/-- Complete interval computation for depth 15, residue 30278. -/
theorem bounds_15_30278 : exactInterval 15 30278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30278 : oddCount 30278 15 = 7 ∧ acceleratedOrbit 15 30278 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30278) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30278.1, data_15_30278.2]

/-- Complete interval computation for depth 15, residue 30279. -/
theorem bounds_15_30279 : exactInterval 15 30279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30279 : oddCount 30279 15 = 7 ∧ acceleratedOrbit 15 30279 = 2021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30279) = 3 ^ 7 * m + 2021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30279.1, data_15_30279.2]

/-- Complete interval computation for depth 15, residue 30280. -/
theorem bounds_15_30280 : exactInterval 15 30280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30280 : oddCount 30280 15 = 7 ∧ acceleratedOrbit 15 30280 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30280) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30280.1, data_15_30280.2]

/-- Complete interval computation for depth 15, residue 30281. -/
theorem bounds_15_30281 : exactInterval 15 30281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30281 : oddCount 30281 15 = 9 ∧ acceleratedOrbit 15 30281 = 18191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30281) = 3 ^ 9 * m + 18191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30281.1, data_15_30281.2]

/-- Complete interval computation for depth 15, residue 30282. -/
theorem bounds_15_30282 : exactInterval 15 30282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30282 : oddCount 30282 15 = 7 ∧ acceleratedOrbit 15 30282 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30282) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30282.1, data_15_30282.2]

/-- Complete interval computation for depth 15, residue 30283. -/
theorem bounds_15_30283 : exactInterval 15 30283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30283 : oddCount 30283 15 = 7 ∧ acceleratedOrbit 15 30283 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30283) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30283.1, data_15_30283.2]

/-- Complete interval computation for depth 15, residue 30284. -/
theorem bounds_15_30284 : exactInterval 15 30284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30284 : oddCount 30284 15 = 7 ∧ acceleratedOrbit 15 30284 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30284) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30284.1, data_15_30284.2]

/-- Complete interval computation for depth 15, residue 30285. -/
theorem bounds_15_30285 : exactInterval 15 30285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30285 : oddCount 30285 15 = 7 ∧ acceleratedOrbit 15 30285 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30285) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30285.1, data_15_30285.2]

/-- Complete interval computation for depth 15, residue 30286. -/
theorem bounds_15_30286 : exactInterval 15 30286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30286 : oddCount 30286 15 = 10 ∧ acceleratedOrbit 15 30286 = 54584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30286) = 3 ^ 10 * m + 54584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30286.1, data_15_30286.2]

/-- Complete interval computation for depth 15, residue 30287. -/
theorem bounds_15_30287 : exactInterval 15 30287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30287 : oddCount 30287 15 = 10 ∧ acceleratedOrbit 15 30287 = 54584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30287) = 3 ^ 10 * m + 54584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30287.1, data_15_30287.2]

/-- Complete interval computation for depth 15, residue 30288. -/
theorem bounds_15_30288 : exactInterval 15 30288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30288 : oddCount 30288 15 = 3 ∧ acceleratedOrbit 15 30288 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30288) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30288.1, data_15_30288.2]

/-- Complete interval computation for depth 15, residue 30289. -/
theorem bounds_15_30289 : exactInterval 15 30289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30289 : oddCount 30289 15 = 10 ∧ acceleratedOrbit 15 30289 = 54593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30289) = 3 ^ 10 * m + 54593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30289.1, data_15_30289.2]

/-- Complete interval computation for depth 15, residue 30290. -/
theorem bounds_15_30290 : exactInterval 15 30290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30290 : oddCount 30290 15 = 10 ∧ acceleratedOrbit 15 30290 = 54593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30290) = 3 ^ 10 * m + 54593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30290.1, data_15_30290.2]

/-- Complete interval computation for depth 15, residue 30291. -/
theorem bounds_15_30291 : exactInterval 15 30291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30291 : oddCount 30291 15 = 10 ∧ acceleratedOrbit 15 30291 = 54593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30291) = 3 ^ 10 * m + 54593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30291.1, data_15_30291.2]

/-- Complete interval computation for depth 15, residue 30292. -/
theorem bounds_15_30292 : exactInterval 15 30292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30292 : oddCount 30292 15 = 3 ∧ acceleratedOrbit 15 30292 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30292) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30292.1, data_15_30292.2]

/-- Complete interval computation for depth 15, residue 30293. -/
theorem bounds_15_30293 : exactInterval 15 30293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30293 : oddCount 30293 15 = 3 ∧ acceleratedOrbit 15 30293 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30293) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30293.1, data_15_30293.2]

/-- Complete interval computation for depth 15, residue 30294. -/
theorem bounds_15_30294 : exactInterval 15 30294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30294 : oddCount 30294 15 = 8 ∧ acceleratedOrbit 15 30294 = 6068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30294) = 3 ^ 8 * m + 6068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30294.1, data_15_30294.2]

/-- Complete interval computation for depth 15, residue 30295. -/
theorem bounds_15_30295 : exactInterval 15 30295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30295 : oddCount 30295 15 = 8 ∧ acceleratedOrbit 15 30295 = 6068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30295) = 3 ^ 8 * m + 6068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30295.1, data_15_30295.2]

/-- Complete interval computation for depth 15, residue 30296. -/
theorem bounds_15_30296 : exactInterval 15 30296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30296 : oddCount 30296 15 = 8 ∧ acceleratedOrbit 15 30296 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30296) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30296.1, data_15_30296.2]

/-- Complete interval computation for depth 15, residue 30297. -/
theorem bounds_15_30297 : exactInterval 15 30297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30297 : oddCount 30297 15 = 8 ∧ acceleratedOrbit 15 30297 = 6068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30297) = 3 ^ 8 * m + 6068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30297.1, data_15_30297.2]

/-- Complete interval computation for depth 15, residue 30298. -/
theorem bounds_15_30298 : exactInterval 15 30298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30298 : oddCount 30298 15 = 8 ∧ acceleratedOrbit 15 30298 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30298) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30298.1, data_15_30298.2]

/-- Complete interval computation for depth 15, residue 30299. -/
theorem bounds_15_30299 : exactInterval 15 30299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30299 : oddCount 30299 15 = 8 ∧ acceleratedOrbit 15 30299 = 6067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30299) = 3 ^ 8 * m + 6067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30299.1, data_15_30299.2]

/-- Complete interval computation for depth 15, residue 30300. -/
theorem bounds_15_30300 : exactInterval 15 30300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30300 : oddCount 30300 15 = 8 ∧ acceleratedOrbit 15 30300 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30300) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30300.1, data_15_30300.2]

/-- Complete interval computation for depth 15, residue 30301. -/
theorem bounds_15_30301 : exactInterval 15 30301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30301 : oddCount 30301 15 = 8 ∧ acceleratedOrbit 15 30301 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30301) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30301.1, data_15_30301.2]

/-- Complete interval computation for depth 15, residue 30302. -/
theorem bounds_15_30302 : exactInterval 15 30302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30302 : oddCount 30302 15 = 8 ∧ acceleratedOrbit 15 30302 = 6068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30302) = 3 ^ 8 * m + 6068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30302.1, data_15_30302.2]

/-- Complete interval computation for depth 15, residue 30303. -/
theorem bounds_15_30303 : exactInterval 15 30303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30303 : oddCount 30303 15 = 8 ∧ acceleratedOrbit 15 30303 = 6068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30303) = 3 ^ 8 * m + 6068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30303.1, data_15_30303.2]

/-- Complete interval computation for depth 15, residue 30304. -/
theorem bounds_15_30304 : exactInterval 15 30304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30304 : oddCount 30304 15 = 3 ∧ acceleratedOrbit 15 30304 = 25 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30304) = 3 ^ 3 * m + 25 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30304.1, data_15_30304.2]

/-- Complete interval computation for depth 15, residue 30305. -/
theorem bounds_15_30305 : exactInterval 15 30305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30305 : oddCount 30305 15 = 7 ∧ acceleratedOrbit 15 30305 = 2024 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30305) = 3 ^ 7 * m + 2024 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30305.1, data_15_30305.2]

/-- Complete interval computation for depth 15, residue 30306. -/
theorem bounds_15_30306 : exactInterval 15 30306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30306 : oddCount 30306 15 = 8 ∧ acceleratedOrbit 15 30306 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30306) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30306.1, data_15_30306.2]

/-- Complete interval computation for depth 15, residue 30307. -/
theorem bounds_15_30307 : exactInterval 15 30307 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30307 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30307) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30307 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30307 : oddCount 30307 15 = 8 ∧ acceleratedOrbit 15 30307 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30307 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30307) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30307.1, data_15_30307.2]

/-- Complete interval computation for depth 15, residue 30308. -/
theorem bounds_15_30308 : exactInterval 15 30308 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30308 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30308) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30308 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30308 : oddCount 30308 15 = 8 ∧ acceleratedOrbit 15 30308 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30308 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30308) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30308.1, data_15_30308.2]

/-- Complete interval computation for depth 15, residue 30309. -/
theorem bounds_15_30309 : exactInterval 15 30309 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30309 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30309) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30309 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30309 : oddCount 30309 15 = 8 ∧ acceleratedOrbit 15 30309 = 6074 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30309 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30309) = 3 ^ 8 * m + 6074 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30309.1, data_15_30309.2]

end Collatz.Research.PassageAtlas.Batch0925
