import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0652

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21331. -/
theorem bounds_15_21331 : exactInterval 15 21331 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21331 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21331) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21331 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21331 : oddCount 21331 15 = 9 ∧ acceleratedOrbit 15 21331 = 12815 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21331 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21331) = 3 ^ 9 * m + 12815 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21331.1, data_15_21331.2]

/-- Complete interval computation for depth 15, residue 21332. -/
theorem bounds_15_21332 : exactInterval 15 21332 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21332 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21332) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21332 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21332 : oddCount 21332 15 = 5 ∧ acceleratedOrbit 15 21332 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21332 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21332) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21332.1, data_15_21332.2]

/-- Complete interval computation for depth 15, residue 21333. -/
theorem bounds_15_21333 : exactInterval 15 21333 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21333 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21333) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21333 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21333 : oddCount 21333 15 = 5 ∧ acceleratedOrbit 15 21333 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21333 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21333) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21333.1, data_15_21333.2]

/-- Complete interval computation for depth 15, residue 21334. -/
theorem bounds_15_21334 : exactInterval 15 21334 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21334 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21334) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21334 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21334 : oddCount 21334 15 = 9 ∧ acceleratedOrbit 15 21334 = 12818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21334 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21334) = 3 ^ 9 * m + 12818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21334.1, data_15_21334.2]

/-- Complete interval computation for depth 15, residue 21335. -/
theorem bounds_15_21335 : exactInterval 15 21335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21335 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21335) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21335 : oddCount 21335 15 = 9 ∧ acceleratedOrbit 15 21335 = 12818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21335 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21335) = 3 ^ 9 * m + 12818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21335.1, data_15_21335.2]

/-- Complete interval computation for depth 15, residue 21336. -/
theorem bounds_15_21336 : exactInterval 15 21336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21336 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21336) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21336 : oddCount 21336 15 = 6 ∧ acceleratedOrbit 15 21336 = 475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21336 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21336) = 3 ^ 6 * m + 475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21336.1, data_15_21336.2]

/-- Complete interval computation for depth 15, residue 21337. -/
theorem bounds_15_21337 : exactInterval 15 21337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21337 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21337) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21337 : oddCount 21337 15 = 6 ∧ acceleratedOrbit 15 21337 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21337 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21337) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21337.1, data_15_21337.2]

/-- Complete interval computation for depth 15, residue 21338. -/
theorem bounds_15_21338 : exactInterval 15 21338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21338 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21338) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21338 : oddCount 21338 15 = 6 ∧ acceleratedOrbit 15 21338 = 475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21338 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21338) = 3 ^ 6 * m + 475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21338.1, data_15_21338.2]

/-- Complete interval computation for depth 15, residue 21339. -/
theorem bounds_15_21339 : exactInterval 15 21339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21339 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21339) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21339 : oddCount 21339 15 = 8 ∧ acceleratedOrbit 15 21339 = 4273 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21339 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21339) = 3 ^ 8 * m + 4273 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21339.1, data_15_21339.2]

/-- Complete interval computation for depth 15, residue 21340. -/
theorem bounds_15_21340 : exactInterval 15 21340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21340 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21340) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21340 : oddCount 21340 15 = 6 ∧ acceleratedOrbit 15 21340 = 475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21340 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21340) = 3 ^ 6 * m + 475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21340.1, data_15_21340.2]

/-- Complete interval computation for depth 15, residue 21341. -/
theorem bounds_15_21341 : exactInterval 15 21341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21341 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21341) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21341 : oddCount 21341 15 = 6 ∧ acceleratedOrbit 15 21341 = 475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21341 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21341) = 3 ^ 6 * m + 475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21341.1, data_15_21341.2]

/-- Complete interval computation for depth 15, residue 21342. -/
theorem bounds_15_21342 : exactInterval 15 21342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21342 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21342) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21342 : oddCount 21342 15 = 9 ∧ acceleratedOrbit 15 21342 = 12824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21342 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21342) = 3 ^ 9 * m + 12824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21342.1, data_15_21342.2]

/-- Complete interval computation for depth 15, residue 21343. -/
theorem bounds_15_21343 : exactInterval 15 21343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21343 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21343) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21343 : oddCount 21343 15 = 9 ∧ acceleratedOrbit 15 21343 = 12824 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21343 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21343) = 3 ^ 9 * m + 12824 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21343.1, data_15_21343.2]

/-- Complete interval computation for depth 15, residue 21344. -/
theorem bounds_15_21344 : exactInterval 15 21344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21344 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21344) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21344 : oddCount 21344 15 = 8 ∧ acceleratedOrbit 15 21344 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21344 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21344) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21344.1, data_15_21344.2]

/-- Complete interval computation for depth 15, residue 21345. -/
theorem bounds_15_21345 : exactInterval 15 21345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21345 : oddCount 21345 15 = 10 ∧ acceleratedOrbit 15 21345 = 38470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21345) = 3 ^ 10 * m + 38470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21345.1, data_15_21345.2]

/-- Complete interval computation for depth 15, residue 21346. -/
theorem bounds_15_21346 : exactInterval 15 21346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21346 : oddCount 21346 15 = 6 ∧ acceleratedOrbit 15 21346 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21346) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21346.1, data_15_21346.2]

/-- Complete interval computation for depth 15, residue 21347. -/
theorem bounds_15_21347 : exactInterval 15 21347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21347 : oddCount 21347 15 = 6 ∧ acceleratedOrbit 15 21347 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21347) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21347.1, data_15_21347.2]

/-- Complete interval computation for depth 15, residue 21348. -/
theorem bounds_15_21348 : exactInterval 15 21348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21348 : oddCount 21348 15 = 6 ∧ acceleratedOrbit 15 21348 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21348) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21348.1, data_15_21348.2]

/-- Complete interval computation for depth 15, residue 21349. -/
theorem bounds_15_21349 : exactInterval 15 21349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21349 : oddCount 21349 15 = 6 ∧ acceleratedOrbit 15 21349 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21349) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21349.1, data_15_21349.2]

/-- Complete interval computation for depth 15, residue 21350. -/
theorem bounds_15_21350 : exactInterval 15 21350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21350 : oddCount 21350 15 = 6 ∧ acceleratedOrbit 15 21350 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21350) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21350.1, data_15_21350.2]

/-- Complete interval computation for depth 15, residue 21351. -/
theorem bounds_15_21351 : exactInterval 15 21351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21351 : oddCount 21351 15 = 11 ∧ acceleratedOrbit 15 21351 = 115433 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21351) = 3 ^ 11 * m + 115433 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21351.1, data_15_21351.2]

/-- Complete interval computation for depth 15, residue 21352. -/
theorem bounds_15_21352 : exactInterval 15 21352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21352 : oddCount 21352 15 = 8 ∧ acceleratedOrbit 15 21352 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21352) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21352.1, data_15_21352.2]

/-- Complete interval computation for depth 15, residue 21353. -/
theorem bounds_15_21353 : exactInterval 15 21353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21353 : oddCount 21353 15 = 8 ∧ acceleratedOrbit 15 21353 = 4276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21353) = 3 ^ 8 * m + 4276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21353.1, data_15_21353.2]

/-- Complete interval computation for depth 15, residue 21354. -/
theorem bounds_15_21354 : exactInterval 15 21354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21354 : oddCount 21354 15 = 8 ∧ acceleratedOrbit 15 21354 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21354) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21354.1, data_15_21354.2]

/-- Complete interval computation for depth 15, residue 21355. -/
theorem bounds_15_21355 : exactInterval 15 21355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21355 : oddCount 21355 15 = 7 ∧ acceleratedOrbit 15 21355 = 1426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21355) = 3 ^ 7 * m + 1426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21355.1, data_15_21355.2]

/-- Complete interval computation for depth 15, residue 21356. -/
theorem bounds_15_21356 : exactInterval 15 21356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21356 : oddCount 21356 15 = 7 ∧ acceleratedOrbit 15 21356 = 1426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21356) = 3 ^ 7 * m + 1426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21356.1, data_15_21356.2]

/-- Complete interval computation for depth 15, residue 21357. -/
theorem bounds_15_21357 : exactInterval 15 21357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21357 : oddCount 21357 15 = 7 ∧ acceleratedOrbit 15 21357 = 1426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21357) = 3 ^ 7 * m + 1426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21357.1, data_15_21357.2]

/-- Complete interval computation for depth 15, residue 21358. -/
theorem bounds_15_21358 : exactInterval 15 21358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21358 : oddCount 21358 15 = 7 ∧ acceleratedOrbit 15 21358 = 1426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21358) = 3 ^ 7 * m + 1426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21358.1, data_15_21358.2]

/-- Complete interval computation for depth 15, residue 21359. -/
theorem bounds_15_21359 : exactInterval 15 21359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21359 : oddCount 21359 15 = 8 ∧ acceleratedOrbit 15 21359 = 4277 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21359) = 3 ^ 8 * m + 4277 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21359.1, data_15_21359.2]

/-- Complete interval computation for depth 15, residue 21360. -/
theorem bounds_15_21360 : exactInterval 15 21360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21360 : oddCount 21360 15 = 8 ∧ acceleratedOrbit 15 21360 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21360) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21360.1, data_15_21360.2]

/-- Complete interval computation for depth 15, residue 21361. -/
theorem bounds_15_21361 : exactInterval 15 21361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21361 : oddCount 21361 15 = 8 ∧ acceleratedOrbit 15 21361 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21361) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21361.1, data_15_21361.2]

/-- Complete interval computation for depth 15, residue 21362. -/
theorem bounds_15_21362 : exactInterval 15 21362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21362 : oddCount 21362 15 = 6 ∧ acceleratedOrbit 15 21362 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21362) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21362.1, data_15_21362.2]

/-- Complete interval computation for depth 15, residue 21363. -/
theorem bounds_15_21363 : exactInterval 15 21363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21363 : oddCount 21363 15 = 6 ∧ acceleratedOrbit 15 21363 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21363) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21363.1, data_15_21363.2]

end Collatz.Research.PassageAtlas.Batch0652
