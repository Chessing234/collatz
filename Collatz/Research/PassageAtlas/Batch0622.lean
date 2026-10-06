import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0622

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20348. -/
theorem bounds_15_20348 : exactInterval 15 20348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20348 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20348) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20348 : oddCount 20348 15 = 9 ∧ acceleratedOrbit 15 20348 = 12226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20348 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20348) = 3 ^ 9 * m + 12226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20348.1, data_15_20348.2]

/-- Complete interval computation for depth 15, residue 20349. -/
theorem bounds_15_20349 : exactInterval 15 20349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20349 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20349) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20349 : oddCount 20349 15 = 9 ∧ acceleratedOrbit 15 20349 = 12226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20349 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20349) = 3 ^ 9 * m + 12226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20349.1, data_15_20349.2]

/-- Complete interval computation for depth 15, residue 20350. -/
theorem bounds_15_20350 : exactInterval 15 20350 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20350 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20350) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20350 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20350 : oddCount 20350 15 = 8 ∧ acceleratedOrbit 15 20350 = 4075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20350 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20350) = 3 ^ 8 * m + 4075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20350.1, data_15_20350.2]

/-- Complete interval computation for depth 15, residue 20351. -/
theorem bounds_15_20351 : exactInterval 15 20351 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20351 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20351) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20351 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20351 : oddCount 20351 15 = 8 ∧ acceleratedOrbit 15 20351 = 4075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20351 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20351) = 3 ^ 8 * m + 4075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20351.1, data_15_20351.2]

/-- Complete interval computation for depth 15, residue 20352. -/
theorem bounds_15_20352 : exactInterval 15 20352 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20352 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20352) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20352 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20352 : oddCount 20352 15 = 7 ∧ acceleratedOrbit 15 20352 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20352 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20352) = 3 ^ 7 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20352.1, data_15_20352.2]

/-- Complete interval computation for depth 15, residue 20353. -/
theorem bounds_15_20353 : exactInterval 15 20353 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20353 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20353) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20353 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20353 : oddCount 20353 15 = 9 ∧ acceleratedOrbit 15 20353 = 12230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20353 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20353) = 3 ^ 9 * m + 12230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20353.1, data_15_20353.2]

/-- Complete interval computation for depth 15, residue 20354. -/
theorem bounds_15_20354 : exactInterval 15 20354 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20354 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20354) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20354 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20354 : oddCount 20354 15 = 5 ∧ acceleratedOrbit 15 20354 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20354 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20354) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20354.1, data_15_20354.2]

/-- Complete interval computation for depth 15, residue 20355. -/
theorem bounds_15_20355 : exactInterval 15 20355 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20355 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20355) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20355 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20355 : oddCount 20355 15 = 5 ∧ acceleratedOrbit 15 20355 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20355 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20355) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20355.1, data_15_20355.2]

/-- Complete interval computation for depth 15, residue 20356. -/
theorem bounds_15_20356 : exactInterval 15 20356 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20356 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20356) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20356 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20356 : oddCount 20356 15 = 8 ∧ acceleratedOrbit 15 20356 = 4078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20356 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20356) = 3 ^ 8 * m + 4078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20356.1, data_15_20356.2]

/-- Complete interval computation for depth 15, residue 20357. -/
theorem bounds_15_20357 : exactInterval 15 20357 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20357 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20357) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20357 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20357 : oddCount 20357 15 = 8 ∧ acceleratedOrbit 15 20357 = 4078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20357 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20357) = 3 ^ 8 * m + 4078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20357.1, data_15_20357.2]

/-- Complete interval computation for depth 15, residue 20358. -/
theorem bounds_15_20358 : exactInterval 15 20358 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20358 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20358) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20358 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20358 : oddCount 20358 15 = 8 ∧ acceleratedOrbit 15 20358 = 4078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20358 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20358) = 3 ^ 8 * m + 4078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20358.1, data_15_20358.2]

/-- Complete interval computation for depth 15, residue 20359. -/
theorem bounds_15_20359 : exactInterval 15 20359 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20359 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20359) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20359 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20359 : oddCount 20359 15 = 5 ∧ acceleratedOrbit 15 20359 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20359 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20359) = 3 ^ 5 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20359.1, data_15_20359.2]

/-- Complete interval computation for depth 15, residue 20360. -/
theorem bounds_15_20360 : exactInterval 15 20360 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20360 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20360) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20360 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20360 : oddCount 20360 15 = 5 ∧ acceleratedOrbit 15 20360 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20360 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20360) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20360.1, data_15_20360.2]

/-- Complete interval computation for depth 15, residue 20361. -/
theorem bounds_15_20361 : exactInterval 15 20361 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20361 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20361) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20361 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20361 : oddCount 20361 15 = 9 ∧ acceleratedOrbit 15 20361 = 12232 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20361 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20361) = 3 ^ 9 * m + 12232 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20361.1, data_15_20361.2]

/-- Complete interval computation for depth 15, residue 20362. -/
theorem bounds_15_20362 : exactInterval 15 20362 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20362 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20362) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20362 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20362 : oddCount 20362 15 = 5 ∧ acceleratedOrbit 15 20362 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20362 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20362) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20362.1, data_15_20362.2]

/-- Complete interval computation for depth 15, residue 20363. -/
theorem bounds_15_20363 : exactInterval 15 20363 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20363 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20363) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20363 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20363 : oddCount 20363 15 = 8 ∧ acceleratedOrbit 15 20363 = 4078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20363 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20363) = 3 ^ 8 * m + 4078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20363.1, data_15_20363.2]

/-- Complete interval computation for depth 15, residue 20364. -/
theorem bounds_15_20364 : exactInterval 15 20364 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20364 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20364) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20364 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20364 : oddCount 20364 15 = 5 ∧ acceleratedOrbit 15 20364 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20364 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20364) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20364.1, data_15_20364.2]

/-- Complete interval computation for depth 15, residue 20365. -/
theorem bounds_15_20365 : exactInterval 15 20365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20365 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20365) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20365 : oddCount 20365 15 = 5 ∧ acceleratedOrbit 15 20365 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20365 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20365) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20365.1, data_15_20365.2]

/-- Complete interval computation for depth 15, residue 20366. -/
theorem bounds_15_20366 : exactInterval 15 20366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20366 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20366) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20366 : oddCount 20366 15 = 8 ∧ acceleratedOrbit 15 20366 = 4079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20366 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20366) = 3 ^ 8 * m + 4079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20366.1, data_15_20366.2]

/-- Complete interval computation for depth 15, residue 20367. -/
theorem bounds_15_20367 : exactInterval 15 20367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20367 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20367) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20367 : oddCount 20367 15 = 8 ∧ acceleratedOrbit 15 20367 = 4079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20367 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20367) = 3 ^ 8 * m + 4079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20367.1, data_15_20367.2]

/-- Complete interval computation for depth 15, residue 20368. -/
theorem bounds_15_20368 : exactInterval 15 20368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20368 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20368) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20368 : oddCount 20368 15 = 6 ∧ acceleratedOrbit 15 20368 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20368 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20368) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20368.1, data_15_20368.2]

/-- Complete interval computation for depth 15, residue 20369. -/
theorem bounds_15_20369 : exactInterval 15 20369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20369 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20369) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20369 : oddCount 20369 15 = 7 ∧ acceleratedOrbit 15 20369 = 1360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20369 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20369) = 3 ^ 7 * m + 1360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20369.1, data_15_20369.2]

/-- Complete interval computation for depth 15, residue 20370. -/
theorem bounds_15_20370 : exactInterval 15 20370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20370 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20370) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20370 : oddCount 20370 15 = 7 ∧ acceleratedOrbit 15 20370 = 1360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20370 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20370) = 3 ^ 7 * m + 1360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20370.1, data_15_20370.2]

/-- Complete interval computation for depth 15, residue 20371. -/
theorem bounds_15_20371 : exactInterval 15 20371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20371 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20371) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20371 : oddCount 20371 15 = 7 ∧ acceleratedOrbit 15 20371 = 1360 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20371 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20371) = 3 ^ 7 * m + 1360 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20371.1, data_15_20371.2]

/-- Complete interval computation for depth 15, residue 20372. -/
theorem bounds_15_20372 : exactInterval 15 20372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20372 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20372) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20372 : oddCount 20372 15 = 6 ∧ acceleratedOrbit 15 20372 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20372 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20372) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20372.1, data_15_20372.2]

/-- Complete interval computation for depth 15, residue 20373. -/
theorem bounds_15_20373 : exactInterval 15 20373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20373 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20373) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20373 : oddCount 20373 15 = 6 ∧ acceleratedOrbit 15 20373 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20373 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20373) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20373.1, data_15_20373.2]

/-- Complete interval computation for depth 15, residue 20374. -/
theorem bounds_15_20374 : exactInterval 15 20374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20374 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20374) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20374 : oddCount 20374 15 = 6 ∧ acceleratedOrbit 15 20374 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20374 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20374) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20374.1, data_15_20374.2]

/-- Complete interval computation for depth 15, residue 20375. -/
theorem bounds_15_20375 : exactInterval 15 20375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20375 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20375) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20375 : oddCount 20375 15 = 6 ∧ acceleratedOrbit 15 20375 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20375 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20375) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20375.1, data_15_20375.2]

/-- Complete interval computation for depth 15, residue 20376. -/
theorem bounds_15_20376 : exactInterval 15 20376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20376 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20376) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20376 : oddCount 20376 15 = 6 ∧ acceleratedOrbit 15 20376 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20376 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20376) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20376.1, data_15_20376.2]

/-- Complete interval computation for depth 15, residue 20377. -/
theorem bounds_15_20377 : exactInterval 15 20377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20377 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20377) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20377 : oddCount 20377 15 = 6 ∧ acceleratedOrbit 15 20377 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20377 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20377) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20377.1, data_15_20377.2]

/-- Complete interval computation for depth 15, residue 20378. -/
theorem bounds_15_20378 : exactInterval 15 20378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20378 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20378) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20378 : oddCount 20378 15 = 6 ∧ acceleratedOrbit 15 20378 = 454 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20378 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20378) = 3 ^ 6 * m + 454 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20378.1, data_15_20378.2]

/-- Complete interval computation for depth 15, residue 20379. -/
theorem bounds_15_20379 : exactInterval 15 20379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20379 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20379) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20379 : oddCount 20379 15 = 8 ∧ acceleratedOrbit 15 20379 = 4081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20379 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20379) = 3 ^ 8 * m + 4081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20379.1, data_15_20379.2]

/-- Complete interval computation for depth 15, residue 20380. -/
theorem bounds_15_20380 : exactInterval 15 20380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20380 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20380) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20380 : oddCount 20380 15 = 7 ∧ acceleratedOrbit 15 20380 = 1361 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20380 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20380) = 3 ^ 7 * m + 1361 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20380.1, data_15_20380.2]

end Collatz.Research.PassageAtlas.Batch0622
