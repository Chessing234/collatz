import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0817

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5365. -/
theorem bounds_13_5365 : exactInterval 13 5365 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5365 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5365) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5365 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5365 : oddCount 5365 13 = 6 ∧ acceleratedOrbit 13 5365 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5365 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5365) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5365.1, data_13_5365.2]

/-- Complete interval computation for depth 13, residue 5366. -/
theorem bounds_13_5366 : exactInterval 13 5366 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5366 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5366) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5366 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5366 : oddCount 5366 13 = 6 ∧ acceleratedOrbit 13 5366 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5366 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5366) = 3 ^ 6 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5366.1, data_13_5366.2]

/-- Complete interval computation for depth 13, residue 5367. -/
theorem bounds_13_5367 : exactInterval 13 5367 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5367 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5367) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5367 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5367 : oddCount 5367 13 = 6 ∧ acceleratedOrbit 13 5367 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5367 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5367) = 3 ^ 6 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5367.1, data_13_5367.2]

/-- Complete interval computation for depth 13, residue 5368. -/
theorem bounds_13_5368 : exactInterval 13 5368 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5368 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5368) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5368 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5368 : oddCount 5368 13 = 8 ∧ acceleratedOrbit 13 5368 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5368 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5368) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5368.1, data_13_5368.2]

/-- Complete interval computation for depth 13, residue 5369. -/
theorem bounds_13_5369 : exactInterval 13 5369 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5369 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5369) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5369 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5369 : oddCount 5369 13 = 6 ∧ acceleratedOrbit 13 5369 = 478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5369 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5369) = 3 ^ 6 * m + 478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5369.1, data_13_5369.2]

/-- Complete interval computation for depth 13, residue 5370. -/
theorem bounds_13_5370 : exactInterval 13 5370 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5370 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5370) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5370 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5370 : oddCount 5370 13 = 8 ∧ acceleratedOrbit 13 5370 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5370 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5370) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5370.1, data_13_5370.2]

/-- Complete interval computation for depth 13, residue 5371. -/
theorem bounds_13_5371 : exactInterval 13 5371 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5371 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5371) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5371 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5371 : oddCount 5371 13 = 8 ∧ acceleratedOrbit 13 5371 = 4303 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5371 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5371) = 3 ^ 8 * m + 4303 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5371.1, data_13_5371.2]

/-- Complete interval computation for depth 13, residue 5372. -/
theorem bounds_13_5372 : exactInterval 13 5372 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5372 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5372) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5372 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5372 : oddCount 5372 13 = 8 ∧ acceleratedOrbit 13 5372 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5372 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5372) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5372.1, data_13_5372.2]

/-- Complete interval computation for depth 13, residue 5373. -/
theorem bounds_13_5373 : exactInterval 13 5373 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5373 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5373) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5373 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5373 : oddCount 5373 13 = 8 ∧ acceleratedOrbit 13 5373 = 4306 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5373 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5373) = 3 ^ 8 * m + 4306 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5373.1, data_13_5373.2]

/-- Complete interval computation for depth 13, residue 5374. -/
theorem bounds_13_5374 : exactInterval 13 5374 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5374 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5374) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5374 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5374 : oddCount 5374 13 = 9 ∧ acceleratedOrbit 13 5374 = 12917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5374 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5374) = 3 ^ 9 * m + 12917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5374.1, data_13_5374.2]

/-- Complete interval computation for depth 13, residue 5375. -/
theorem bounds_13_5375 : exactInterval 13 5375 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5375 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5375) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5375 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5375 : oddCount 5375 13 = 9 ∧ acceleratedOrbit 13 5375 = 12917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5375 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5375) = 3 ^ 9 * m + 12917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5375.1, data_13_5375.2]

/-- Complete interval computation for depth 13, residue 5376. -/
theorem bounds_13_5376 : exactInterval 13 5376 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5376 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5376) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5376 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5376 : oddCount 5376 13 = 1 ∧ acceleratedOrbit 13 5376 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5376 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5376) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5376.1, data_13_5376.2]

/-- Complete interval computation for depth 13, residue 5377. -/
theorem bounds_13_5377 : exactInterval 13 5377 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5377 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5377) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5377 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5377 : oddCount 5377 13 = 6 ∧ acceleratedOrbit 13 5377 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5377 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5377) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5377.1, data_13_5377.2]

/-- Complete interval computation for depth 13, residue 5378. -/
theorem bounds_13_5378 : exactInterval 13 5378 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5378 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5378) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5378 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5378 : oddCount 5378 13 = 8 ∧ acceleratedOrbit 13 5378 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5378 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5378) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5378.1, data_13_5378.2]

/-- Complete interval computation for depth 13, residue 5379. -/
theorem bounds_13_5379 : exactInterval 13 5379 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5379 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5379) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5379 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5379 : oddCount 5379 13 = 8 ∧ acceleratedOrbit 13 5379 = 4313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5379 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5379) = 3 ^ 8 * m + 4313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5379.1, data_13_5379.2]

/-- Complete interval computation for depth 13, residue 5380. -/
theorem bounds_13_5380 : exactInterval 13 5380 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5380 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5380) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5380 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5380 : oddCount 5380 13 = 5 ∧ acceleratedOrbit 13 5380 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5380 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5380) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5380.1, data_13_5380.2]

end Collatz.Research.StoppingAtlas.Batch0817
