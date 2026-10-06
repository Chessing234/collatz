import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0753

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4382. -/
theorem bounds_13_4382 : exactInterval 13 4382 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4382 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4382) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4382 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4382 : oddCount 4382 13 = 7 ∧ acceleratedOrbit 13 4382 = 1171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4382 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4382) = 3 ^ 7 * m + 1171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4382.1, data_13_4382.2]

/-- Complete interval computation for depth 13, residue 4383. -/
theorem bounds_13_4383 : exactInterval 13 4383 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4383 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4383) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4383 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4383 : oddCount 4383 13 = 8 ∧ acceleratedOrbit 13 4383 = 3512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4383 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4383) = 3 ^ 8 * m + 3512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4383.1, data_13_4383.2]

/-- Complete interval computation for depth 13, residue 4384. -/
theorem bounds_13_4384 : exactInterval 13 4384 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4384 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4384) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4384 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4384 : oddCount 4384 13 = 6 ∧ acceleratedOrbit 13 4384 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4384 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4384) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4384.1, data_13_4384.2]

/-- Complete interval computation for depth 13, residue 4385. -/
theorem bounds_13_4385 : exactInterval 13 4385 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4385 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4385) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4385 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4385 : oddCount 4385 13 = 6 ∧ acceleratedOrbit 13 4385 = 391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4385 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4385) = 3 ^ 6 * m + 391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4385.1, data_13_4385.2]

/-- Complete interval computation for depth 13, residue 4386. -/
theorem bounds_13_4386 : exactInterval 13 4386 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4386 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4386) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4386 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4386 : oddCount 4386 13 = 7 ∧ acceleratedOrbit 13 4386 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4386 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4386) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4386.1, data_13_4386.2]

/-- Complete interval computation for depth 13, residue 4387. -/
theorem bounds_13_4387 : exactInterval 13 4387 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4387 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4387) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4387 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4387 : oddCount 4387 13 = 7 ∧ acceleratedOrbit 13 4387 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4387 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4387) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4387.1, data_13_4387.2]

/-- Complete interval computation for depth 13, residue 4388. -/
theorem bounds_13_4388 : exactInterval 13 4388 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4388 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4388) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4388 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4388 : oddCount 4388 13 = 7 ∧ acceleratedOrbit 13 4388 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4388 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4388) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4388.1, data_13_4388.2]

/-- Complete interval computation for depth 13, residue 4389. -/
theorem bounds_13_4389 : exactInterval 13 4389 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4389 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4389) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4389 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4389 : oddCount 4389 13 = 7 ∧ acceleratedOrbit 13 4389 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4389 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4389) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4389.1, data_13_4389.2]

/-- Complete interval computation for depth 13, residue 4390. -/
theorem bounds_13_4390 : exactInterval 13 4390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4390 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4390) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4390 : oddCount 4390 13 = 7 ∧ acceleratedOrbit 13 4390 = 1174 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4390 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4390) = 3 ^ 7 * m + 1174 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4390.1, data_13_4390.2]

/-- Complete interval computation for depth 13, residue 4391. -/
theorem bounds_13_4391 : exactInterval 13 4391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4391 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4391) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4391 : oddCount 4391 13 = 9 ∧ acceleratedOrbit 13 4391 = 10556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4391 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4391) = 3 ^ 9 * m + 10556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4391.1, data_13_4391.2]

/-- Complete interval computation for depth 13, residue 4392. -/
theorem bounds_13_4392 : exactInterval 13 4392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4392 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4392) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4392 : oddCount 4392 13 = 6 ∧ acceleratedOrbit 13 4392 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4392 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4392) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4392.1, data_13_4392.2]

/-- Complete interval computation for depth 13, residue 4393. -/
theorem bounds_13_4393 : exactInterval 13 4393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4393 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4393) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4393 : oddCount 4393 13 = 8 ∧ acceleratedOrbit 13 4393 = 3520 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4393 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4393) = 3 ^ 8 * m + 3520 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4393.1, data_13_4393.2]

/-- Complete interval computation for depth 13, residue 4394. -/
theorem bounds_13_4394 : exactInterval 13 4394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4394 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4394) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4394 : oddCount 4394 13 = 6 ∧ acceleratedOrbit 13 4394 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4394 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4394) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4394.1, data_13_4394.2]

/-- Complete interval computation for depth 13, residue 4395. -/
theorem bounds_13_4395 : exactInterval 13 4395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4395 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4395) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4395 : oddCount 4395 13 = 8 ∧ acceleratedOrbit 13 4395 = 3523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4395 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4395) = 3 ^ 8 * m + 3523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4395.1, data_13_4395.2]

/-- Complete interval computation for depth 13, residue 4396. -/
theorem bounds_13_4396 : exactInterval 13 4396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4396 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4396) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4396 : oddCount 4396 13 = 4 ∧ acceleratedOrbit 13 4396 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4396 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4396) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4396.1, data_13_4396.2]

/-- Complete interval computation for depth 13, residue 4397. -/
theorem bounds_13_4397 : exactInterval 13 4397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4397 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4397) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4397 : oddCount 4397 13 = 4 ∧ acceleratedOrbit 13 4397 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4397 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4397) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4397.1, data_13_4397.2]

end Collatz.Research.StoppingAtlas.Batch0753
