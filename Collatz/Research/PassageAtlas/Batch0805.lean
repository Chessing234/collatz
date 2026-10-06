import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0805

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26345. -/
theorem bounds_15_26345 : exactInterval 15 26345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26345 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26345) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26345 : oddCount 26345 15 = 10 ∧ acceleratedOrbit 15 26345 = 47479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26345 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26345) = 3 ^ 10 * m + 47479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26345.1, data_15_26345.2]

/-- Complete interval computation for depth 15, residue 26346. -/
theorem bounds_15_26346 : exactInterval 15 26346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26346 : oddCount 26346 15 = 6 ∧ acceleratedOrbit 15 26346 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26346) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26346.1, data_15_26346.2]

/-- Complete interval computation for depth 15, residue 26347. -/
theorem bounds_15_26347 : exactInterval 15 26347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26347 : oddCount 26347 15 = 8 ∧ acceleratedOrbit 15 26347 = 5276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26347) = 3 ^ 8 * m + 5276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26347.1, data_15_26347.2]

/-- Complete interval computation for depth 15, residue 26348. -/
theorem bounds_15_26348 : exactInterval 15 26348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26348 : oddCount 26348 15 = 8 ∧ acceleratedOrbit 15 26348 = 5278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26348) = 3 ^ 8 * m + 5278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26348.1, data_15_26348.2]

/-- Complete interval computation for depth 15, residue 26349. -/
theorem bounds_15_26349 : exactInterval 15 26349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26349 : oddCount 26349 15 = 8 ∧ acceleratedOrbit 15 26349 = 5278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26349) = 3 ^ 8 * m + 5278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26349.1, data_15_26349.2]

/-- Complete interval computation for depth 15, residue 26350. -/
theorem bounds_15_26350 : exactInterval 15 26350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26350 : oddCount 26350 15 = 8 ∧ acceleratedOrbit 15 26350 = 5278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26350) = 3 ^ 8 * m + 5278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26350.1, data_15_26350.2]

/-- Complete interval computation for depth 15, residue 26351. -/
theorem bounds_15_26351 : exactInterval 15 26351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26351 : oddCount 26351 15 = 10 ∧ acceleratedOrbit 15 26351 = 47488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26351) = 3 ^ 10 * m + 47488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26351.1, data_15_26351.2]

/-- Complete interval computation for depth 15, residue 26352. -/
theorem bounds_15_26352 : exactInterval 15 26352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26352 : oddCount 26352 15 = 7 ∧ acceleratedOrbit 15 26352 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26352) = 3 ^ 7 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26352.1, data_15_26352.2]

/-- Complete interval computation for depth 15, residue 26353. -/
theorem bounds_15_26353 : exactInterval 15 26353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26353 : oddCount 26353 15 = 6 ∧ acceleratedOrbit 15 26353 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26353) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26353.1, data_15_26353.2]

/-- Complete interval computation for depth 15, residue 26354. -/
theorem bounds_15_26354 : exactInterval 15 26354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26354 : oddCount 26354 15 = 9 ∧ acceleratedOrbit 15 26354 = 15833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26354) = 3 ^ 9 * m + 15833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26354.1, data_15_26354.2]

/-- Complete interval computation for depth 15, residue 26355. -/
theorem bounds_15_26355 : exactInterval 15 26355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26355 : oddCount 26355 15 = 9 ∧ acceleratedOrbit 15 26355 = 15833 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26355) = 3 ^ 9 * m + 15833 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26355.1, data_15_26355.2]

/-- Complete interval computation for depth 15, residue 26356. -/
theorem bounds_15_26356 : exactInterval 15 26356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26356 : oddCount 26356 15 = 7 ∧ acceleratedOrbit 15 26356 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26356) = 3 ^ 7 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26356.1, data_15_26356.2]

/-- Complete interval computation for depth 15, residue 26357. -/
theorem bounds_15_26357 : exactInterval 15 26357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26357 : oddCount 26357 15 = 7 ∧ acceleratedOrbit 15 26357 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26357) = 3 ^ 7 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26357.1, data_15_26357.2]

/-- Complete interval computation for depth 15, residue 26358. -/
theorem bounds_15_26358 : exactInterval 15 26358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26358 : oddCount 26358 15 = 10 ∧ acceleratedOrbit 15 26358 = 47506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26358) = 3 ^ 10 * m + 47506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26358.1, data_15_26358.2]

/-- Complete interval computation for depth 15, residue 26359. -/
theorem bounds_15_26359 : exactInterval 15 26359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26359 : oddCount 26359 15 = 10 ∧ acceleratedOrbit 15 26359 = 47506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26359) = 3 ^ 10 * m + 47506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26359.1, data_15_26359.2]

/-- Complete interval computation for depth 15, residue 26360. -/
theorem bounds_15_26360 : exactInterval 15 26360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26360 : oddCount 26360 15 = 7 ∧ acceleratedOrbit 15 26360 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26360) = 3 ^ 7 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26360.1, data_15_26360.2]

/-- Complete interval computation for depth 15, residue 26361. -/
theorem bounds_15_26361 : exactInterval 15 26361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26361 : oddCount 26361 15 = 6 ∧ acceleratedOrbit 15 26361 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26361) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26361.1, data_15_26361.2]

/-- Complete interval computation for depth 15, residue 26362. -/
theorem bounds_15_26362 : exactInterval 15 26362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26362 : oddCount 26362 15 = 7 ∧ acceleratedOrbit 15 26362 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26362) = 3 ^ 7 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26362.1, data_15_26362.2]

/-- Complete interval computation for depth 15, residue 26363. -/
theorem bounds_15_26363 : exactInterval 15 26363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26363 : oddCount 26363 15 = 8 ∧ acceleratedOrbit 15 26363 = 5279 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26363) = 3 ^ 8 * m + 5279 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26363.1, data_15_26363.2]

/-- Complete interval computation for depth 15, residue 26364. -/
theorem bounds_15_26364 : exactInterval 15 26364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26364 : oddCount 26364 15 = 11 ∧ acceleratedOrbit 15 26364 = 142550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26364) = 3 ^ 11 * m + 142550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26364.1, data_15_26364.2]

/-- Complete interval computation for depth 15, residue 26365. -/
theorem bounds_15_26365 : exactInterval 15 26365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26365 : oddCount 26365 15 = 11 ∧ acceleratedOrbit 15 26365 = 142550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26365) = 3 ^ 11 * m + 142550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26365.1, data_15_26365.2]

/-- Complete interval computation for depth 15, residue 26366. -/
theorem bounds_15_26366 : exactInterval 15 26366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26366 : oddCount 26366 15 = 11 ∧ acceleratedOrbit 15 26366 = 142550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26366) = 3 ^ 11 * m + 142550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26366.1, data_15_26366.2]

/-- Complete interval computation for depth 15, residue 26367. -/
theorem bounds_15_26367 : exactInterval 15 26367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26367 : oddCount 26367 15 = 10 ∧ acceleratedOrbit 15 26367 = 47516 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26367) = 3 ^ 10 * m + 47516 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26367.1, data_15_26367.2]

/-- Complete interval computation for depth 15, residue 26368. -/
theorem bounds_15_26368 : exactInterval 15 26368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26368 : oddCount 26368 15 = 6 ∧ acceleratedOrbit 15 26368 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26368) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26368.1, data_15_26368.2]

/-- Complete interval computation for depth 15, residue 26369. -/
theorem bounds_15_26369 : exactInterval 15 26369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26369 : oddCount 26369 15 = 6 ∧ acceleratedOrbit 15 26369 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26369) = 3 ^ 6 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26369.1, data_15_26369.2]

/-- Complete interval computation for depth 15, residue 26370. -/
theorem bounds_15_26370 : exactInterval 15 26370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26370 : oddCount 26370 15 = 8 ∧ acceleratedOrbit 15 26370 = 5282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26370) = 3 ^ 8 * m + 5282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26370.1, data_15_26370.2]

/-- Complete interval computation for depth 15, residue 26371. -/
theorem bounds_15_26371 : exactInterval 15 26371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26371 : oddCount 26371 15 = 8 ∧ acceleratedOrbit 15 26371 = 5282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26371) = 3 ^ 8 * m + 5282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26371.1, data_15_26371.2]

/-- Complete interval computation for depth 15, residue 26372. -/
theorem bounds_15_26372 : exactInterval 15 26372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26372 : oddCount 26372 15 = 8 ∧ acceleratedOrbit 15 26372 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26372) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26372.1, data_15_26372.2]

/-- Complete interval computation for depth 15, residue 26373. -/
theorem bounds_15_26373 : exactInterval 15 26373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26373 : oddCount 26373 15 = 8 ∧ acceleratedOrbit 15 26373 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26373) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26373.1, data_15_26373.2]

/-- Complete interval computation for depth 15, residue 26374. -/
theorem bounds_15_26374 : exactInterval 15 26374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26374 : oddCount 26374 15 = 8 ∧ acceleratedOrbit 15 26374 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26374) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26374.1, data_15_26374.2]

/-- Complete interval computation for depth 15, residue 26375. -/
theorem bounds_15_26375 : exactInterval 15 26375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26375 : oddCount 26375 15 = 8 ∧ acceleratedOrbit 15 26375 = 5282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26375) = 3 ^ 8 * m + 5282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26375.1, data_15_26375.2]

/-- Complete interval computation for depth 15, residue 26376. -/
theorem bounds_15_26376 : exactInterval 15 26376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26376 : oddCount 26376 15 = 8 ∧ acceleratedOrbit 15 26376 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26376) = 3 ^ 8 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26376.1, data_15_26376.2]

/-- Complete interval computation for depth 15, residue 26377. -/
theorem bounds_15_26377 : exactInterval 15 26377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26377 : oddCount 26377 15 = 10 ∧ acceleratedOrbit 15 26377 = 47537 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26377) = 3 ^ 10 * m + 47537 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26377.1, data_15_26377.2]

end Collatz.Research.PassageAtlas.Batch0805
