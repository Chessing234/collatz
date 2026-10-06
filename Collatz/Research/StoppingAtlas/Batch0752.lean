import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0752

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4367. -/
theorem bounds_13_4367 : exactInterval 13 4367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4367 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4367) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4367 : oddCount 4367 13 = 6 ∧ acceleratedOrbit 13 4367 = 389 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4367 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4367) = 3 ^ 6 * m + 389 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4367.1, data_13_4367.2]

/-- Complete interval computation for depth 13, residue 4368. -/
theorem bounds_13_4368 : exactInterval 13 4368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4368 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4368) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4368 : oddCount 4368 13 = 4 ∧ acceleratedOrbit 13 4368 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4368 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4368) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4368.1, data_13_4368.2]

/-- Complete interval computation for depth 13, residue 4369. -/
theorem bounds_13_4369 : exactInterval 13 4369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4369 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4369) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4369 : oddCount 4369 13 = 5 ∧ acceleratedOrbit 13 4369 = 130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4369 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4369) = 3 ^ 5 * m + 130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4369.1, data_13_4369.2]

/-- Complete interval computation for depth 13, residue 4370. -/
theorem bounds_13_4370 : exactInterval 13 4370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4370 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4370) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4370 : oddCount 4370 13 = 8 ∧ acceleratedOrbit 13 4370 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4370 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4370) = 3 ^ 8 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4370.1, data_13_4370.2]

/-- Complete interval computation for depth 13, residue 4371. -/
theorem bounds_13_4371 : exactInterval 13 4371 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4371 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4371) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4371 : oddCount 4371 13 = 8 ∧ acceleratedOrbit 13 4371 = 3503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4371 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4371) = 3 ^ 8 * m + 3503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4371.1, data_13_4371.2]

/-- Complete interval computation for depth 13, residue 4372. -/
theorem bounds_13_4372 : exactInterval 13 4372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4372 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4372) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4372 : oddCount 4372 13 = 4 ∧ acceleratedOrbit 13 4372 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4372 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4372) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4372.1, data_13_4372.2]

/-- Complete interval computation for depth 13, residue 4373. -/
theorem bounds_13_4373 : exactInterval 13 4373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4373 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4373) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4373 : oddCount 4373 13 = 4 ∧ acceleratedOrbit 13 4373 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4373 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4373) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4373.1, data_13_4373.2]

/-- Complete interval computation for depth 13, residue 4374. -/
theorem bounds_13_4374 : exactInterval 13 4374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4374 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4374) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4374 : oddCount 4374 13 = 8 ∧ acceleratedOrbit 13 4374 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4374 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4374) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4374.1, data_13_4374.2]

/-- Complete interval computation for depth 13, residue 4375. -/
theorem bounds_13_4375 : exactInterval 13 4375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4375 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4375) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4375 : oddCount 4375 13 = 8 ∧ acceleratedOrbit 13 4375 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4375 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4375) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4375.1, data_13_4375.2]

/-- Complete interval computation for depth 13, residue 4376. -/
theorem bounds_13_4376 : exactInterval 13 4376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4376 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4376) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4376 : oddCount 4376 13 = 4 ∧ acceleratedOrbit 13 4376 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4376 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4376) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4376.1, data_13_4376.2]

/-- Complete interval computation for depth 13, residue 4377. -/
theorem bounds_13_4377 : exactInterval 13 4377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4377 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4377) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4377 : oddCount 4377 13 = 8 ∧ acceleratedOrbit 13 4377 = 3509 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4377 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4377) = 3 ^ 8 * m + 3509 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4377.1, data_13_4377.2]

/-- Complete interval computation for depth 13, residue 4378. -/
theorem bounds_13_4378 : exactInterval 13 4378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4378 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4378) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4378 : oddCount 4378 13 = 4 ∧ acceleratedOrbit 13 4378 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4378 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4378) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4378.1, data_13_4378.2]

/-- Complete interval computation for depth 13, residue 4379. -/
theorem bounds_13_4379 : exactInterval 13 4379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4379 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4379) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4379 : oddCount 4379 13 = 9 ∧ acceleratedOrbit 13 4379 = 10525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4379 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4379) = 3 ^ 9 * m + 10525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4379.1, data_13_4379.2]

/-- Complete interval computation for depth 13, residue 4380. -/
theorem bounds_13_4380 : exactInterval 13 4380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4380 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4380) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4380 : oddCount 4380 13 = 7 ∧ acceleratedOrbit 13 4380 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4380 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4380) = 3 ^ 7 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4380.1, data_13_4380.2]

/-- Complete interval computation for depth 13, residue 4381. -/
theorem bounds_13_4381 : exactInterval 13 4381 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4381 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4381) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4381 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4381 : oddCount 4381 13 = 7 ∧ acceleratedOrbit 13 4381 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4381 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4381) = 3 ^ 7 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4381.1, data_13_4381.2]

end Collatz.Research.StoppingAtlas.Batch0752
