import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0622

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2370. -/
theorem bounds_13_2370 : exactInterval 13 2370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2370 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2370) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2370 : oddCount 2370 13 = 8 ∧ acceleratedOrbit 13 2370 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2370 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2370) = 3 ^ 8 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2370.1, data_13_2370.2]

/-- Complete interval computation for depth 13, residue 2371. -/
theorem bounds_13_2371 : exactInterval 13 2371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2371 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2371) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2371 : oddCount 2371 13 = 8 ∧ acceleratedOrbit 13 2371 = 1903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2371 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2371) = 3 ^ 8 * m + 1903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2371.1, data_13_2371.2]

/-- Complete interval computation for depth 13, residue 2372. -/
theorem bounds_13_2372 : exactInterval 13 2372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2372 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2372) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2372 : oddCount 2372 13 = 7 ∧ acceleratedOrbit 13 2372 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2372 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2372) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2372.1, data_13_2372.2]

/-- Complete interval computation for depth 13, residue 2373. -/
theorem bounds_13_2373 : exactInterval 13 2373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2373 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2373) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2373 : oddCount 2373 13 = 7 ∧ acceleratedOrbit 13 2373 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2373 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2373) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2373.1, data_13_2373.2]

/-- Complete interval computation for depth 13, residue 2374. -/
theorem bounds_13_2374 : exactInterval 13 2374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2374 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2374) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2374 : oddCount 2374 13 = 7 ∧ acceleratedOrbit 13 2374 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2374 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2374) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2374.1, data_13_2374.2]

/-- Complete interval computation for depth 13, residue 2375. -/
theorem bounds_13_2375 : exactInterval 13 2375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2375 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2375) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2375 : oddCount 2375 13 = 10 ∧ acceleratedOrbit 13 2375 = 17131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2375 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2375) = 3 ^ 10 * m + 17131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2375.1, data_13_2375.2]

/-- Complete interval computation for depth 13, residue 2376. -/
theorem bounds_13_2376 : exactInterval 13 2376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2376 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2376) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2376 : oddCount 2376 13 = 7 ∧ acceleratedOrbit 13 2376 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2376 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2376) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2376.1, data_13_2376.2]

/-- Complete interval computation for depth 13, residue 2377. -/
theorem bounds_13_2377 : exactInterval 13 2377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2377 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2377) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2377 : oddCount 2377 13 = 8 ∧ acceleratedOrbit 13 2377 = 1907 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2377 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2377) = 3 ^ 8 * m + 1907 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2377.1, data_13_2377.2]

/-- Complete interval computation for depth 13, residue 2378. -/
theorem bounds_13_2378 : exactInterval 13 2378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2378 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2378) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2378 : oddCount 2378 13 = 7 ∧ acceleratedOrbit 13 2378 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2378 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2378) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2378.1, data_13_2378.2]

/-- Complete interval computation for depth 13, residue 2379. -/
theorem bounds_13_2379 : exactInterval 13 2379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2379 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2379) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2379 : oddCount 2379 13 = 7 ∧ acceleratedOrbit 13 2379 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2379 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2379) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2379.1, data_13_2379.2]

/-- Complete interval computation for depth 13, residue 2380. -/
theorem bounds_13_2380 : exactInterval 13 2380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2380 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2380) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2380 : oddCount 2380 13 = 7 ∧ acceleratedOrbit 13 2380 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2380 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2380) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2380.1, data_13_2380.2]

/-- Complete interval computation for depth 13, residue 2381. -/
theorem bounds_13_2381 : exactInterval 13 2381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2381 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2381) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2381 : oddCount 2381 13 = 7 ∧ acceleratedOrbit 13 2381 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2381 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2381) = 3 ^ 7 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2381.1, data_13_2381.2]

/-- Complete interval computation for depth 13, residue 2382. -/
theorem bounds_13_2382 : exactInterval 13 2382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2382 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2382) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2382 : oddCount 2382 13 = 8 ∧ acceleratedOrbit 13 2382 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2382 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2382) = 3 ^ 8 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2382.1, data_13_2382.2]

/-- Complete interval computation for depth 13, residue 2383. -/
theorem bounds_13_2383 : exactInterval 13 2383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2383 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2383) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2383 : oddCount 2383 13 = 8 ∧ acceleratedOrbit 13 2383 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2383 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2383) = 3 ^ 8 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2383.1, data_13_2383.2]

/-- Complete interval computation for depth 13, residue 2384. -/
theorem bounds_13_2384 : exactInterval 13 2384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2384 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2384) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2384 : oddCount 2384 13 = 4 ∧ acceleratedOrbit 13 2384 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2384 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2384) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2384.1, data_13_2384.2]

end Collatz.Research.StoppingAtlas.Batch0622
