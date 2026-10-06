import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0623

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2385. -/
theorem bounds_13_2385 : exactInterval 13 2385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2385 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2385) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2385 : oddCount 2385 13 = 9 ∧ acceleratedOrbit 13 2385 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2385 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2385) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2385.1, data_13_2385.2]

/-- Complete interval computation for depth 13, residue 2386. -/
theorem bounds_13_2386 : exactInterval 13 2386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2386 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2386) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2386 : oddCount 2386 13 = 9 ∧ acceleratedOrbit 13 2386 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2386 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2386) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2386.1, data_13_2386.2]

/-- Complete interval computation for depth 13, residue 2387. -/
theorem bounds_13_2387 : exactInterval 13 2387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2387 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2387) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2387 : oddCount 2387 13 = 9 ∧ acceleratedOrbit 13 2387 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2387 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2387) = 3 ^ 9 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2387.1, data_13_2387.2]

/-- Complete interval computation for depth 13, residue 2388. -/
theorem bounds_13_2388 : exactInterval 13 2388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2388 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2388) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2388 : oddCount 2388 13 = 4 ∧ acceleratedOrbit 13 2388 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2388 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2388) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2388.1, data_13_2388.2]

/-- Complete interval computation for depth 13, residue 2389. -/
theorem bounds_13_2389 : exactInterval 13 2389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2389 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2389) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2389 : oddCount 2389 13 = 4 ∧ acceleratedOrbit 13 2389 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2389 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2389) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2389.1, data_13_2389.2]

/-- Complete interval computation for depth 13, residue 2390. -/
theorem bounds_13_2390 : exactInterval 13 2390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2390 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2390) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2390 : oddCount 2390 13 = 5 ∧ acceleratedOrbit 13 2390 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2390 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2390) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2390.1, data_13_2390.2]

/-- Complete interval computation for depth 13, residue 2391. -/
theorem bounds_13_2391 : exactInterval 13 2391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2391 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2391) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2391 : oddCount 2391 13 = 5 ∧ acceleratedOrbit 13 2391 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2391 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2391) = 3 ^ 5 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2391.1, data_13_2391.2]

/-- Complete interval computation for depth 13, residue 2392. -/
theorem bounds_13_2392 : exactInterval 13 2392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2392 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2392) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2392 : oddCount 2392 13 = 6 ∧ acceleratedOrbit 13 2392 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2392 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2392) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2392.1, data_13_2392.2]

/-- Complete interval computation for depth 13, residue 2393. -/
theorem bounds_13_2393 : exactInterval 13 2393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2393 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2393) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2393 : oddCount 2393 13 = 7 ∧ acceleratedOrbit 13 2393 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2393 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2393) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2393.1, data_13_2393.2]

/-- Complete interval computation for depth 13, residue 2394. -/
theorem bounds_13_2394 : exactInterval 13 2394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2394 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2394) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2394 : oddCount 2394 13 = 6 ∧ acceleratedOrbit 13 2394 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2394 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2394) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2394.1, data_13_2394.2]

/-- Complete interval computation for depth 13, residue 2395. -/
theorem bounds_13_2395 : exactInterval 13 2395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2395 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2395) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2395 : oddCount 2395 13 = 7 ∧ acceleratedOrbit 13 2395 = 640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2395 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2395) = 3 ^ 7 * m + 640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2395.1, data_13_2395.2]

/-- Complete interval computation for depth 13, residue 2396. -/
theorem bounds_13_2396 : exactInterval 13 2396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2396 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2396) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2396 : oddCount 2396 13 = 6 ∧ acceleratedOrbit 13 2396 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2396 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2396) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2396.1, data_13_2396.2]

/-- Complete interval computation for depth 13, residue 2397. -/
theorem bounds_13_2397 : exactInterval 13 2397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2397 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2397) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2397 : oddCount 2397 13 = 6 ∧ acceleratedOrbit 13 2397 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2397 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2397) = 3 ^ 6 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2397.1, data_13_2397.2]

/-- Complete interval computation for depth 13, residue 2398. -/
theorem bounds_13_2398 : exactInterval 13 2398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2398 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2398) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2398 : oddCount 2398 13 = 7 ∧ acceleratedOrbit 13 2398 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2398 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2398) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2398.1, data_13_2398.2]

/-- Complete interval computation for depth 13, residue 2399. -/
theorem bounds_13_2399 : exactInterval 13 2399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2399 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2399) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2399 : oddCount 2399 13 = 7 ∧ acceleratedOrbit 13 2399 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2399 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2399) = 3 ^ 7 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2399.1, data_13_2399.2]

/-- Complete interval computation for depth 13, residue 2400. -/
theorem bounds_13_2400 : exactInterval 13 2400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2400 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2400) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2400 : oddCount 2400 13 = 3 ∧ acceleratedOrbit 13 2400 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2400 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2400) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2400.1, data_13_2400.2]

end Collatz.Research.StoppingAtlas.Batch0623
