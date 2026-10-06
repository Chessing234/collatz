import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0356

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2380. -/
theorem bounds_12_2380 : exactInterval 12 2380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2380 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2380) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2380 : oddCount 2380 12 = 6 ∧ acceleratedOrbit 12 2380 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2380 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2380) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2380.1, data_12_2380.2]

/-- Complete interval computation for depth 12, residue 2381. -/
theorem bounds_12_2381 : exactInterval 12 2381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2381 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2381) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2381 : oddCount 2381 12 = 6 ∧ acceleratedOrbit 12 2381 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2381 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2381) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2381.1, data_12_2381.2]

/-- Complete interval computation for depth 12, residue 2382. -/
theorem bounds_12_2382 : exactInterval 12 2382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2382 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2382) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2382 : oddCount 2382 12 = 8 ∧ acceleratedOrbit 12 2382 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2382 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2382) = 3 ^ 8 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2382.1, data_12_2382.2]

/-- Complete interval computation for depth 12, residue 2383. -/
theorem bounds_12_2383 : exactInterval 12 2383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2383 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2383) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2383 : oddCount 2383 12 = 8 ∧ acceleratedOrbit 12 2383 = 3820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2383 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2383) = 3 ^ 8 * m + 3820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2383.1, data_12_2383.2]

/-- Complete interval computation for depth 12, residue 2384. -/
theorem bounds_12_2384 : exactInterval 12 2384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2384 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2384) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2384 : oddCount 2384 12 = 3 ∧ acceleratedOrbit 12 2384 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2384 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2384) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2384.1, data_12_2384.2]

/-- Complete interval computation for depth 12, residue 2385. -/
theorem bounds_12_2385 : exactInterval 12 2385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2385 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2385) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2385 : oddCount 2385 12 = 8 ∧ acceleratedOrbit 12 2385 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2385 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2385) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2385.1, data_12_2385.2]

/-- Complete interval computation for depth 12, residue 2386. -/
theorem bounds_12_2386 : exactInterval 12 2386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2386 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2386) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2386 : oddCount 2386 12 = 8 ∧ acceleratedOrbit 12 2386 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2386 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2386) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2386.1, data_12_2386.2]

/-- Complete interval computation for depth 12, residue 2387. -/
theorem bounds_12_2387 : exactInterval 12 2387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2387 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2387) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2387 : oddCount 2387 12 = 8 ∧ acceleratedOrbit 12 2387 = 3827 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2387 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2387) = 3 ^ 8 * m + 3827 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2387.1, data_12_2387.2]

/-- Complete interval computation for depth 12, residue 2388. -/
theorem bounds_12_2388 : exactInterval 12 2388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2388 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2388) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2388 : oddCount 2388 12 = 3 ∧ acceleratedOrbit 12 2388 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2388 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2388) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2388.1, data_12_2388.2]

/-- Complete interval computation for depth 12, residue 2389. -/
theorem bounds_12_2389 : exactInterval 12 2389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2389 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2389) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2389 : oddCount 2389 12 = 3 ∧ acceleratedOrbit 12 2389 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2389 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2389) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2389.1, data_12_2389.2]

/-- Complete interval computation for depth 12, residue 2390. -/
theorem bounds_12_2390 : exactInterval 12 2390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2390 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2390) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2390 : oddCount 2390 12 = 5 ∧ acceleratedOrbit 12 2390 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2390 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2390) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2390.1, data_12_2390.2]

/-- Complete interval computation for depth 12, residue 2391. -/
theorem bounds_12_2391 : exactInterval 12 2391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2391 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2391) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2391 : oddCount 2391 12 = 5 ∧ acceleratedOrbit 12 2391 = 142 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2391 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2391) = 3 ^ 5 * m + 142 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2391.1, data_12_2391.2]

/-- Complete interval computation for depth 12, residue 2392. -/
theorem bounds_12_2392 : exactInterval 12 2392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2392 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2392) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2392 : oddCount 2392 12 = 5 ∧ acceleratedOrbit 12 2392 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2392 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2392) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2392.1, data_12_2392.2]

/-- Complete interval computation for depth 12, residue 2393. -/
theorem bounds_12_2393 : exactInterval 12 2393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2393 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2393) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2393 : oddCount 2393 12 = 6 ∧ acceleratedOrbit 12 2393 = 427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2393 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2393) = 3 ^ 6 * m + 427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2393.1, data_12_2393.2]

/-- Complete interval computation for depth 12, residue 2394. -/
theorem bounds_12_2394 : exactInterval 12 2394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2394 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2394) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2394 : oddCount 2394 12 = 5 ∧ acceleratedOrbit 12 2394 = 143 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2394 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2394) = 3 ^ 5 * m + 143 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2394.1, data_12_2394.2]

/-- Complete interval computation for depth 12, residue 2395. -/
theorem bounds_12_2395 : exactInterval 12 2395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2395 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2395) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2395 : oddCount 2395 12 = 7 ∧ acceleratedOrbit 12 2395 = 1280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2395 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2395) = 3 ^ 7 * m + 1280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2395.1, data_12_2395.2]

end Collatz.Research.StoppingAtlas.Batch0356
