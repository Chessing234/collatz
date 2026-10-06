import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0744

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24346. -/
theorem bounds_15_24346 : exactInterval 15 24346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24346 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24346) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24346 : oddCount 24346 15 = 5 ∧ acceleratedOrbit 15 24346 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24346 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24346) = 3 ^ 5 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24346.1, data_15_24346.2]

/-- Complete interval computation for depth 15, residue 24347. -/
theorem bounds_15_24347 : exactInterval 15 24347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24347 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24347) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24347 : oddCount 24347 15 = 11 ∧ acceleratedOrbit 15 24347 = 131630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24347 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24347) = 3 ^ 11 * m + 131630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24347.1, data_15_24347.2]

/-- Complete interval computation for depth 15, residue 24348. -/
theorem bounds_15_24348 : exactInterval 15 24348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24348 : oddCount 24348 15 = 8 ∧ acceleratedOrbit 15 24348 = 4877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24348) = 3 ^ 8 * m + 4877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24348.1, data_15_24348.2]

/-- Complete interval computation for depth 15, residue 24349. -/
theorem bounds_15_24349 : exactInterval 15 24349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24349 : oddCount 24349 15 = 8 ∧ acceleratedOrbit 15 24349 = 4877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24349) = 3 ^ 8 * m + 4877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24349.1, data_15_24349.2]

/-- Complete interval computation for depth 15, residue 24350. -/
theorem bounds_15_24350 : exactInterval 15 24350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24350 : oddCount 24350 15 = 8 ∧ acceleratedOrbit 15 24350 = 4877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24350) = 3 ^ 8 * m + 4877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24350.1, data_15_24350.2]

/-- Complete interval computation for depth 15, residue 24351. -/
theorem bounds_15_24351 : exactInterval 15 24351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24351 : oddCount 24351 15 = 8 ∧ acceleratedOrbit 15 24351 = 4876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24351) = 3 ^ 8 * m + 4876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24351.1, data_15_24351.2]

/-- Complete interval computation for depth 15, residue 24352. -/
theorem bounds_15_24352 : exactInterval 15 24352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24352 : oddCount 24352 15 = 5 ∧ acceleratedOrbit 15 24352 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24352) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24352.1, data_15_24352.2]

/-- Complete interval computation for depth 15, residue 24353. -/
theorem bounds_15_24353 : exactInterval 15 24353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24353 : oddCount 24353 15 = 6 ∧ acceleratedOrbit 15 24353 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24353) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24353.1, data_15_24353.2]

/-- Complete interval computation for depth 15, residue 24354. -/
theorem bounds_15_24354 : exactInterval 15 24354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24354 : oddCount 24354 15 = 8 ∧ acceleratedOrbit 15 24354 = 4880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24354) = 3 ^ 8 * m + 4880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24354.1, data_15_24354.2]

/-- Complete interval computation for depth 15, residue 24355. -/
theorem bounds_15_24355 : exactInterval 15 24355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24355 : oddCount 24355 15 = 8 ∧ acceleratedOrbit 15 24355 = 4880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24355) = 3 ^ 8 * m + 4880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24355.1, data_15_24355.2]

/-- Complete interval computation for depth 15, residue 24356. -/
theorem bounds_15_24356 : exactInterval 15 24356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24356 : oddCount 24356 15 = 8 ∧ acceleratedOrbit 15 24356 = 4880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24356) = 3 ^ 8 * m + 4880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24356.1, data_15_24356.2]

/-- Complete interval computation for depth 15, residue 24357. -/
theorem bounds_15_24357 : exactInterval 15 24357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24357 : oddCount 24357 15 = 8 ∧ acceleratedOrbit 15 24357 = 4880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24357) = 3 ^ 8 * m + 4880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24357.1, data_15_24357.2]

/-- Complete interval computation for depth 15, residue 24358. -/
theorem bounds_15_24358 : exactInterval 15 24358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24358 : oddCount 24358 15 = 8 ∧ acceleratedOrbit 15 24358 = 4880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24358) = 3 ^ 8 * m + 4880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24358.1, data_15_24358.2]

/-- Complete interval computation for depth 15, residue 24359. -/
theorem bounds_15_24359 : exactInterval 15 24359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24359 : oddCount 24359 15 = 10 ∧ acceleratedOrbit 15 24359 = 43901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24359) = 3 ^ 10 * m + 43901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24359.1, data_15_24359.2]

/-- Complete interval computation for depth 15, residue 24360. -/
theorem bounds_15_24360 : exactInterval 15 24360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24360 : oddCount 24360 15 = 5 ∧ acceleratedOrbit 15 24360 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24360) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24360.1, data_15_24360.2]

/-- Complete interval computation for depth 15, residue 24361. -/
theorem bounds_15_24361 : exactInterval 15 24361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24361 : oddCount 24361 15 = 6 ∧ acceleratedOrbit 15 24361 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24361) = 3 ^ 6 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24361.1, data_15_24361.2]

/-- Complete interval computation for depth 15, residue 24362. -/
theorem bounds_15_24362 : exactInterval 15 24362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24362 : oddCount 24362 15 = 5 ∧ acceleratedOrbit 15 24362 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24362) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24362.1, data_15_24362.2]

/-- Complete interval computation for depth 15, residue 24363. -/
theorem bounds_15_24363 : exactInterval 15 24363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24363 : oddCount 24363 15 = 8 ∧ acceleratedOrbit 15 24363 = 4880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24363) = 3 ^ 8 * m + 4880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24363.1, data_15_24363.2]

/-- Complete interval computation for depth 15, residue 24364. -/
theorem bounds_15_24364 : exactInterval 15 24364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24364 : oddCount 24364 15 = 5 ∧ acceleratedOrbit 15 24364 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24364) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24364.1, data_15_24364.2]

/-- Complete interval computation for depth 15, residue 24365. -/
theorem bounds_15_24365 : exactInterval 15 24365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24365 : oddCount 24365 15 = 5 ∧ acceleratedOrbit 15 24365 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24365) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24365.1, data_15_24365.2]

/-- Complete interval computation for depth 15, residue 24366. -/
theorem bounds_15_24366 : exactInterval 15 24366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24366 : oddCount 24366 15 = 5 ∧ acceleratedOrbit 15 24366 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24366) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24366.1, data_15_24366.2]

/-- Complete interval computation for depth 15, residue 24367. -/
theorem bounds_15_24367 : exactInterval 15 24367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24367 : oddCount 24367 15 = 8 ∧ acceleratedOrbit 15 24367 = 4880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24367) = 3 ^ 8 * m + 4880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24367.1, data_15_24367.2]

/-- Complete interval computation for depth 15, residue 24368. -/
theorem bounds_15_24368 : exactInterval 15 24368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24368 : oddCount 24368 15 = 5 ∧ acceleratedOrbit 15 24368 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24368) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24368.1, data_15_24368.2]

/-- Complete interval computation for depth 15, residue 24369. -/
theorem bounds_15_24369 : exactInterval 15 24369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24369 : oddCount 24369 15 = 5 ∧ acceleratedOrbit 15 24369 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24369) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24369.1, data_15_24369.2]

/-- Complete interval computation for depth 15, residue 24370. -/
theorem bounds_15_24370 : exactInterval 15 24370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24370 : oddCount 24370 15 = 5 ∧ acceleratedOrbit 15 24370 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24370) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24370.1, data_15_24370.2]

/-- Complete interval computation for depth 15, residue 24371. -/
theorem bounds_15_24371 : exactInterval 15 24371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24371 : oddCount 24371 15 = 5 ∧ acceleratedOrbit 15 24371 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24371) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24371.1, data_15_24371.2]

/-- Complete interval computation for depth 15, residue 24372. -/
theorem bounds_15_24372 : exactInterval 15 24372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24372 : oddCount 24372 15 = 5 ∧ acceleratedOrbit 15 24372 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24372) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24372.1, data_15_24372.2]

/-- Complete interval computation for depth 15, residue 24373. -/
theorem bounds_15_24373 : exactInterval 15 24373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24373 : oddCount 24373 15 = 5 ∧ acceleratedOrbit 15 24373 = 181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24373) = 3 ^ 5 * m + 181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24373.1, data_15_24373.2]

/-- Complete interval computation for depth 15, residue 24374. -/
theorem bounds_15_24374 : exactInterval 15 24374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24374 : oddCount 24374 15 = 7 ∧ acceleratedOrbit 15 24374 = 1627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24374) = 3 ^ 7 * m + 1627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24374.1, data_15_24374.2]

/-- Complete interval computation for depth 15, residue 24375. -/
theorem bounds_15_24375 : exactInterval 15 24375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24375 : oddCount 24375 15 = 7 ∧ acceleratedOrbit 15 24375 = 1627 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24375) = 3 ^ 7 * m + 1627 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24375.1, data_15_24375.2]

/-- Complete interval computation for depth 15, residue 24376. -/
theorem bounds_15_24376 : exactInterval 15 24376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24376 : oddCount 24376 15 = 7 ∧ acceleratedOrbit 15 24376 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24376) = 3 ^ 7 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24376.1, data_15_24376.2]

/-- Complete interval computation for depth 15, residue 24377. -/
theorem bounds_15_24377 : exactInterval 15 24377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24377 : oddCount 24377 15 = 8 ∧ acceleratedOrbit 15 24377 = 4882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24377) = 3 ^ 8 * m + 4882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24377.1, data_15_24377.2]

/-- Complete interval computation for depth 15, residue 24378. -/
theorem bounds_15_24378 : exactInterval 15 24378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24378 : oddCount 24378 15 = 7 ∧ acceleratedOrbit 15 24378 = 1628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24378) = 3 ^ 7 * m + 1628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24378.1, data_15_24378.2]

end Collatz.Research.PassageAtlas.Batch0744
