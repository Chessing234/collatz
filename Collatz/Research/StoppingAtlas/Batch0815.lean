import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0815

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5335. -/
theorem bounds_13_5335 : exactInterval 13 5335 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5335 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5335) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5335 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5335 : oddCount 5335 13 = 6 ∧ acceleratedOrbit 13 5335 = 475 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5335 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5335) = 3 ^ 6 * m + 475 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5335.1, data_13_5335.2]

/-- Complete interval computation for depth 13, residue 5336. -/
theorem bounds_13_5336 : exactInterval 13 5336 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5336 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5336) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5336 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5336 : oddCount 5336 13 = 8 ∧ acceleratedOrbit 13 5336 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5336 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5336) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5336.1, data_13_5336.2]

/-- Complete interval computation for depth 13, residue 5337. -/
theorem bounds_13_5337 : exactInterval 13 5337 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5337 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5337) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5337 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5337 : oddCount 5337 13 = 6 ∧ acceleratedOrbit 13 5337 = 476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5337 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5337) = 3 ^ 6 * m + 476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5337.1, data_13_5337.2]

/-- Complete interval computation for depth 13, residue 5338. -/
theorem bounds_13_5338 : exactInterval 13 5338 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5338 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5338) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5338 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5338 : oddCount 5338 13 = 8 ∧ acceleratedOrbit 13 5338 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5338 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5338) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5338.1, data_13_5338.2]

/-- Complete interval computation for depth 13, residue 5339. -/
theorem bounds_13_5339 : exactInterval 13 5339 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5339 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5339) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5339 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5339 : oddCount 5339 13 = 7 ∧ acceleratedOrbit 13 5339 = 1426 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5339 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5339) = 3 ^ 7 * m + 1426 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5339.1, data_13_5339.2]

/-- Complete interval computation for depth 13, residue 5340. -/
theorem bounds_13_5340 : exactInterval 13 5340 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5340 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5340) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5340 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5340 : oddCount 5340 13 = 8 ∧ acceleratedOrbit 13 5340 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5340 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5340) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5340.1, data_13_5340.2]

/-- Complete interval computation for depth 13, residue 5341. -/
theorem bounds_13_5341 : exactInterval 13 5341 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5341 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5341) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5341 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5341 : oddCount 5341 13 = 8 ∧ acceleratedOrbit 13 5341 = 4283 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5341 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5341) = 3 ^ 8 * m + 4283 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5341.1, data_13_5341.2]

/-- Complete interval computation for depth 13, residue 5342. -/
theorem bounds_13_5342 : exactInterval 13 5342 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5342 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5342) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5342 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5342 : oddCount 5342 13 = 9 ∧ acceleratedOrbit 13 5342 = 12842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5342 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5342) = 3 ^ 9 * m + 12842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5342.1, data_13_5342.2]

/-- Complete interval computation for depth 13, residue 5343. -/
theorem bounds_13_5343 : exactInterval 13 5343 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5343 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5343) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5343 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5343 : oddCount 5343 13 = 9 ∧ acceleratedOrbit 13 5343 = 12842 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5343 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5343) = 3 ^ 9 * m + 12842 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5343.1, data_13_5343.2]

/-- Complete interval computation for depth 13, residue 5344. -/
theorem bounds_13_5344 : exactInterval 13 5344 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5344 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5344) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5344 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5344 : oddCount 5344 13 = 6 ∧ acceleratedOrbit 13 5344 = 479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5344 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5344) = 3 ^ 6 * m + 479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5344.1, data_13_5344.2]

/-- Complete interval computation for depth 13, residue 5345. -/
theorem bounds_13_5345 : exactInterval 13 5345 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5345 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5345) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5345 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5345 : oddCount 5345 13 = 10 ∧ acceleratedOrbit 13 5345 = 38546 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5345 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5345) = 3 ^ 10 * m + 38546 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5345.1, data_13_5345.2]

/-- Complete interval computation for depth 13, residue 5346. -/
theorem bounds_13_5346 : exactInterval 13 5346 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5346 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5346) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5346 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5346 : oddCount 5346 13 = 5 ∧ acceleratedOrbit 13 5346 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5346 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5346) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5346.1, data_13_5346.2]

/-- Complete interval computation for depth 13, residue 5347. -/
theorem bounds_13_5347 : exactInterval 13 5347 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5347 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5347) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5347 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5347 : oddCount 5347 13 = 5 ∧ acceleratedOrbit 13 5347 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5347 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5347) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5347.1, data_13_5347.2]

/-- Complete interval computation for depth 13, residue 5348. -/
theorem bounds_13_5348 : exactInterval 13 5348 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5348 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5348) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5348 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5348 : oddCount 5348 13 = 8 ∧ acceleratedOrbit 13 5348 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5348 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5348) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5348.1, data_13_5348.2]

/-- Complete interval computation for depth 13, residue 5349. -/
theorem bounds_13_5349 : exactInterval 13 5349 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5349 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5349) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5349 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5349 : oddCount 5349 13 = 8 ∧ acceleratedOrbit 13 5349 = 4292 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5349 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5349) = 3 ^ 8 * m + 4292 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5349.1, data_13_5349.2]

end Collatz.Research.StoppingAtlas.Batch0815
