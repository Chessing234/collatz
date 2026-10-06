import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0223

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7274. -/
theorem bounds_15_7274 : exactInterval 15 7274 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7274 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7274) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7274 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7274 : oddCount 7274 15 = 2 ∧ acceleratedOrbit 15 7274 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7274 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7274) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7274.1, data_15_7274.2]

/-- Complete interval computation for depth 15, residue 7275. -/
theorem bounds_15_7275 : exactInterval 15 7275 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7275 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7275) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7275 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7275 : oddCount 7275 15 = 10 ∧ acceleratedOrbit 15 7275 = 13115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7275 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7275) = 3 ^ 10 * m + 13115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7275.1, data_15_7275.2]

/-- Complete interval computation for depth 15, residue 7276. -/
theorem bounds_15_7276 : exactInterval 15 7276 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7276 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7276) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7276 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7276 : oddCount 7276 15 = 12 ∧ acceleratedOrbit 15 7276 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7276 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7276) = 3 ^ 12 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7276.1, data_15_7276.2]

/-- Complete interval computation for depth 15, residue 7277. -/
theorem bounds_15_7277 : exactInterval 15 7277 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7277 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7277) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7277 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7277 : oddCount 7277 15 = 12 ∧ acceleratedOrbit 15 7277 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7277 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7277) = 3 ^ 12 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7277.1, data_15_7277.2]

/-- Complete interval computation for depth 15, residue 7278. -/
theorem bounds_15_7278 : exactInterval 15 7278 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7278 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7278) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7278 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7278 : oddCount 7278 15 = 12 ∧ acceleratedOrbit 15 7278 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7278 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7278) = 3 ^ 12 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7278.1, data_15_7278.2]

/-- Complete interval computation for depth 15, residue 7279. -/
theorem bounds_15_7279 : exactInterval 15 7279 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7279 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7279) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7279 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7279 : oddCount 7279 15 = 11 ∧ acceleratedOrbit 15 7279 = 39359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7279 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7279) = 3 ^ 11 * m + 39359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7279.1, data_15_7279.2]

/-- Complete interval computation for depth 15, residue 7280. -/
theorem bounds_15_7280 : exactInterval 15 7280 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7280 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7280) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7280 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7280 : oddCount 7280 15 = 7 ∧ acceleratedOrbit 15 7280 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7280 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7280) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7280.1, data_15_7280.2]

/-- Complete interval computation for depth 15, residue 7281. -/
theorem bounds_15_7281 : exactInterval 15 7281 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7281 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7281) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7281 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7281 : oddCount 7281 15 = 2 ∧ acceleratedOrbit 15 7281 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7281 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7281) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7281.1, data_15_7281.2]

/-- Complete interval computation for depth 15, residue 7282. -/
theorem bounds_15_7282 : exactInterval 15 7282 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7282 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7282) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7282 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7282 : oddCount 7282 15 = 8 ∧ acceleratedOrbit 15 7282 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7282 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7282) = 3 ^ 8 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7282.1, data_15_7282.2]

/-- Complete interval computation for depth 15, residue 7283. -/
theorem bounds_15_7283 : exactInterval 15 7283 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7283 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7283) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7283 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7283 : oddCount 7283 15 = 8 ∧ acceleratedOrbit 15 7283 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7283 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7283) = 3 ^ 8 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7283.1, data_15_7283.2]

/-- Complete interval computation for depth 15, residue 7284. -/
theorem bounds_15_7284 : exactInterval 15 7284 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7284 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7284) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7284 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7284 : oddCount 7284 15 = 7 ∧ acceleratedOrbit 15 7284 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7284 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7284) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7284.1, data_15_7284.2]

/-- Complete interval computation for depth 15, residue 7285. -/
theorem bounds_15_7285 : exactInterval 15 7285 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7285 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7285) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7285 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7285 : oddCount 7285 15 = 7 ∧ acceleratedOrbit 15 7285 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7285 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7285) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7285.1, data_15_7285.2]

/-- Complete interval computation for depth 15, residue 7286. -/
theorem bounds_15_7286 : exactInterval 15 7286 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7286 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7286) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7286 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7286 : oddCount 7286 15 = 7 ∧ acceleratedOrbit 15 7286 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7286 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7286) = 3 ^ 7 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7286.1, data_15_7286.2]

/-- Complete interval computation for depth 15, residue 7287. -/
theorem bounds_15_7287 : exactInterval 15 7287 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7287 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7287) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7287 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7287 : oddCount 7287 15 = 7 ∧ acceleratedOrbit 15 7287 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7287 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7287) = 3 ^ 7 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7287.1, data_15_7287.2]

/-- Complete interval computation for depth 15, residue 7288. -/
theorem bounds_15_7288 : exactInterval 15 7288 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7288 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7288) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7288 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7288 : oddCount 7288 15 = 7 ∧ acceleratedOrbit 15 7288 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7288 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7288) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7288.1, data_15_7288.2]

/-- Complete interval computation for depth 15, residue 7289. -/
theorem bounds_15_7289 : exactInterval 15 7289 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7289 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7289) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7289 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7289 : oddCount 7289 15 = 8 ∧ acceleratedOrbit 15 7289 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7289 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7289) = 3 ^ 8 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7289.1, data_15_7289.2]

/-- Complete interval computation for depth 15, residue 7290. -/
theorem bounds_15_7290 : exactInterval 15 7290 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7290 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7290) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7290 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7290 : oddCount 7290 15 = 7 ∧ acceleratedOrbit 15 7290 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7290 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7290) = 3 ^ 7 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7290.1, data_15_7290.2]

/-- Complete interval computation for depth 15, residue 7291. -/
theorem bounds_15_7291 : exactInterval 15 7291 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7291 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7291) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7291 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7291 : oddCount 7291 15 = 7 ∧ acceleratedOrbit 15 7291 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7291 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7291) = 3 ^ 7 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7291.1, data_15_7291.2]

/-- Complete interval computation for depth 15, residue 7292. -/
theorem bounds_15_7292 : exactInterval 15 7292 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7292 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7292) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7292 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7292 : oddCount 7292 15 = 7 ∧ acceleratedOrbit 15 7292 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7292 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7292) = 3 ^ 7 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7292.1, data_15_7292.2]

/-- Complete interval computation for depth 15, residue 7293. -/
theorem bounds_15_7293 : exactInterval 15 7293 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7293 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7293) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7293 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7293 : oddCount 7293 15 = 7 ∧ acceleratedOrbit 15 7293 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7293 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7293) = 3 ^ 7 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7293.1, data_15_7293.2]

/-- Complete interval computation for depth 15, residue 7294. -/
theorem bounds_15_7294 : exactInterval 15 7294 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7294 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7294) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7294 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7294 : oddCount 7294 15 = 7 ∧ acceleratedOrbit 15 7294 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7294 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7294) = 3 ^ 7 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7294.1, data_15_7294.2]

/-- Complete interval computation for depth 15, residue 7295. -/
theorem bounds_15_7295 : exactInterval 15 7295 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7295 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7295) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7295 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7295 : oddCount 7295 15 = 12 ∧ acceleratedOrbit 15 7295 = 118331 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7295 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7295) = 3 ^ 12 * m + 118331 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7295.1, data_15_7295.2]

/-- Complete interval computation for depth 15, residue 7296. -/
theorem bounds_15_7296 : exactInterval 15 7296 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7296 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7296) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7296 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7296 : oddCount 7296 15 = 5 ∧ acceleratedOrbit 15 7296 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7296 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7296) = 3 ^ 5 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7296.1, data_15_7296.2]

/-- Complete interval computation for depth 15, residue 7297. -/
theorem bounds_15_7297 : exactInterval 15 7297 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7297 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7297) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7297 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7297 : oddCount 7297 15 = 8 ∧ acceleratedOrbit 15 7297 = 1462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7297 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7297) = 3 ^ 8 * m + 1462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7297.1, data_15_7297.2]

/-- Complete interval computation for depth 15, residue 7298. -/
theorem bounds_15_7298 : exactInterval 15 7298 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7298 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7298) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7298 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7298 : oddCount 7298 15 = 6 ∧ acceleratedOrbit 15 7298 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7298 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7298) = 3 ^ 6 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7298.1, data_15_7298.2]

/-- Complete interval computation for depth 15, residue 7299. -/
theorem bounds_15_7299 : exactInterval 15 7299 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7299 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7299) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7299 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7299 : oddCount 7299 15 = 6 ∧ acceleratedOrbit 15 7299 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7299 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7299) = 3 ^ 6 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7299.1, data_15_7299.2]

/-- Complete interval computation for depth 15, residue 7300. -/
theorem bounds_15_7300 : exactInterval 15 7300 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7300 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7300) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7300 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7300 : oddCount 7300 15 = 6 ∧ acceleratedOrbit 15 7300 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7300 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7300) = 3 ^ 6 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7300.1, data_15_7300.2]

/-- Complete interval computation for depth 15, residue 7301. -/
theorem bounds_15_7301 : exactInterval 15 7301 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7301 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7301) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7301 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7301 : oddCount 7301 15 = 6 ∧ acceleratedOrbit 15 7301 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7301 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7301) = 3 ^ 6 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7301.1, data_15_7301.2]

/-- Complete interval computation for depth 15, residue 7302. -/
theorem bounds_15_7302 : exactInterval 15 7302 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7302 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7302) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7302 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7302 : oddCount 7302 15 = 6 ∧ acceleratedOrbit 15 7302 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7302 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7302) = 3 ^ 6 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7302.1, data_15_7302.2]

/-- Complete interval computation for depth 15, residue 7303. -/
theorem bounds_15_7303 : exactInterval 15 7303 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7303 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7303) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7303 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7303 : oddCount 7303 15 = 8 ∧ acceleratedOrbit 15 7303 = 1463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7303 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7303) = 3 ^ 8 * m + 1463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7303.1, data_15_7303.2]

/-- Complete interval computation for depth 15, residue 7304. -/
theorem bounds_15_7304 : exactInterval 15 7304 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7304 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7304) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7304 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7304 : oddCount 7304 15 = 6 ∧ acceleratedOrbit 15 7304 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7304 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7304) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7304.1, data_15_7304.2]

/-- Complete interval computation for depth 15, residue 7305. -/
theorem bounds_15_7305 : exactInterval 15 7305 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7305 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7305) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7305 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7305 : oddCount 7305 15 = 11 ∧ acceleratedOrbit 15 7305 = 39503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7305 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7305) = 3 ^ 11 * m + 39503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7305.1, data_15_7305.2]

/-- Complete interval computation for depth 15, residue 7306. -/
theorem bounds_15_7306 : exactInterval 15 7306 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7306 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7306) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7306 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7306 : oddCount 7306 15 = 6 ∧ acceleratedOrbit 15 7306 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7306 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7306) = 3 ^ 6 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7306.1, data_15_7306.2]

end Collatz.Research.PassageAtlas.Batch0223
