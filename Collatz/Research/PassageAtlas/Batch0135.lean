import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0135

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4390. -/
theorem bounds_15_4390 : exactInterval 15 4390 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4390 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4390) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4390 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4390 : oddCount 4390 15 = 8 ∧ acceleratedOrbit 15 4390 = 881 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4390 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4390) = 3 ^ 8 * m + 881 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4390.1, data_15_4390.2]

/-- Complete interval computation for depth 15, residue 4391. -/
theorem bounds_15_4391 : exactInterval 15 4391 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4391 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4391) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4391 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4391 : oddCount 4391 15 = 9 ∧ acceleratedOrbit 15 4391 = 2639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4391 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4391) = 3 ^ 9 * m + 2639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4391.1, data_15_4391.2]

/-- Complete interval computation for depth 15, residue 4392. -/
theorem bounds_15_4392 : exactInterval 15 4392 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4392 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4392) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4392 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4392 : oddCount 4392 15 = 8 ∧ acceleratedOrbit 15 4392 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4392 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4392) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4392.1, data_15_4392.2]

/-- Complete interval computation for depth 15, residue 4393. -/
theorem bounds_15_4393 : exactInterval 15 4393 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4393 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4393) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4393 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4393 : oddCount 4393 15 = 8 ∧ acceleratedOrbit 15 4393 = 880 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4393 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4393) = 3 ^ 8 * m + 880 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4393.1, data_15_4393.2]

/-- Complete interval computation for depth 15, residue 4394. -/
theorem bounds_15_4394 : exactInterval 15 4394 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4394 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4394) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4394 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4394 : oddCount 4394 15 = 8 ∧ acceleratedOrbit 15 4394 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4394 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4394) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4394.1, data_15_4394.2]

/-- Complete interval computation for depth 15, residue 4395. -/
theorem bounds_15_4395 : exactInterval 15 4395 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4395 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4395) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4395 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4395 : oddCount 4395 15 = 10 ∧ acceleratedOrbit 15 4395 = 7928 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4395 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4395) = 3 ^ 10 * m + 7928 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4395.1, data_15_4395.2]

/-- Complete interval computation for depth 15, residue 4396. -/
theorem bounds_15_4396 : exactInterval 15 4396 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4396 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4396) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4396 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4396 : oddCount 4396 15 = 4 ∧ acceleratedOrbit 15 4396 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4396 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4396) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4396.1, data_15_4396.2]

/-- Complete interval computation for depth 15, residue 4397. -/
theorem bounds_15_4397 : exactInterval 15 4397 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4397 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4397) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4397 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4397 : oddCount 4397 15 = 4 ∧ acceleratedOrbit 15 4397 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4397 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4397) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4397.1, data_15_4397.2]

/-- Complete interval computation for depth 15, residue 4398. -/
theorem bounds_15_4398 : exactInterval 15 4398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4398 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4398) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4398 : oddCount 4398 15 = 4 ∧ acceleratedOrbit 15 4398 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4398 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4398) = 3 ^ 4 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4398.1, data_15_4398.2]

/-- Complete interval computation for depth 15, residue 4399. -/
theorem bounds_15_4399 : exactInterval 15 4399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4399 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4399) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4399 : oddCount 4399 15 = 10 ∧ acceleratedOrbit 15 4399 = 7931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4399 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4399) = 3 ^ 10 * m + 7931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4399.1, data_15_4399.2]

/-- Complete interval computation for depth 15, residue 4400. -/
theorem bounds_15_4400 : exactInterval 15 4400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4400 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4400) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4400 : oddCount 4400 15 = 8 ∧ acceleratedOrbit 15 4400 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4400 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4400) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4400.1, data_15_4400.2]

/-- Complete interval computation for depth 15, residue 4401. -/
theorem bounds_15_4401 : exactInterval 15 4401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4401 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4401) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4401 : oddCount 4401 15 = 8 ∧ acceleratedOrbit 15 4401 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4401 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4401) = 3 ^ 8 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4401.1, data_15_4401.2]

/-- Complete interval computation for depth 15, residue 4402. -/
theorem bounds_15_4402 : exactInterval 15 4402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4402 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4402) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4402 : oddCount 4402 15 = 8 ∧ acceleratedOrbit 15 4402 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4402 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4402) = 3 ^ 8 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4402.1, data_15_4402.2]

/-- Complete interval computation for depth 15, residue 4403. -/
theorem bounds_15_4403 : exactInterval 15 4403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4403 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4403) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4403 : oddCount 4403 15 = 8 ∧ acceleratedOrbit 15 4403 = 884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4403 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4403) = 3 ^ 8 * m + 884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4403.1, data_15_4403.2]

/-- Complete interval computation for depth 15, residue 4404. -/
theorem bounds_15_4404 : exactInterval 15 4404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4404 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4404) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4404 : oddCount 4404 15 = 8 ∧ acceleratedOrbit 15 4404 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4404 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4404) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4404.1, data_15_4404.2]

/-- Complete interval computation for depth 15, residue 4405. -/
theorem bounds_15_4405 : exactInterval 15 4405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4405 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4405) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4405 : oddCount 4405 15 = 8 ∧ acceleratedOrbit 15 4405 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4405 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4405) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4405.1, data_15_4405.2]

/-- Complete interval computation for depth 15, residue 4406. -/
theorem bounds_15_4406 : exactInterval 15 4406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4406 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4406) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4406 : oddCount 4406 15 = 8 ∧ acceleratedOrbit 15 4406 = 883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4406 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4406) = 3 ^ 8 * m + 883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4406.1, data_15_4406.2]

/-- Complete interval computation for depth 15, residue 4407. -/
theorem bounds_15_4407 : exactInterval 15 4407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4407 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4407) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4407 : oddCount 4407 15 = 8 ∧ acceleratedOrbit 15 4407 = 883 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4407 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4407) = 3 ^ 8 * m + 883 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4407.1, data_15_4407.2]

/-- Complete interval computation for depth 15, residue 4408. -/
theorem bounds_15_4408 : exactInterval 15 4408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4408 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4408) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4408 : oddCount 4408 15 = 7 ∧ acceleratedOrbit 15 4408 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4408 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4408) = 3 ^ 7 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4408.1, data_15_4408.2]

/-- Complete interval computation for depth 15, residue 4409. -/
theorem bounds_15_4409 : exactInterval 15 4409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4409 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4409) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4409 : oddCount 4409 15 = 10 ∧ acceleratedOrbit 15 4409 = 7951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4409 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4409) = 3 ^ 10 * m + 7951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4409.1, data_15_4409.2]

/-- Complete interval computation for depth 15, residue 4410. -/
theorem bounds_15_4410 : exactInterval 15 4410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4410 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4410) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4410 : oddCount 4410 15 = 7 ∧ acceleratedOrbit 15 4410 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4410 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4410) = 3 ^ 7 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4410.1, data_15_4410.2]

/-- Complete interval computation for depth 15, residue 4411. -/
theorem bounds_15_4411 : exactInterval 15 4411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4411 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4411) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4411 : oddCount 4411 15 = 7 ∧ acceleratedOrbit 15 4411 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4411 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4411) = 3 ^ 7 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4411.1, data_15_4411.2]

/-- Complete interval computation for depth 15, residue 4412. -/
theorem bounds_15_4412 : exactInterval 15 4412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4412 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4412) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4412 : oddCount 4412 15 = 7 ∧ acceleratedOrbit 15 4412 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4412 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4412) = 3 ^ 7 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4412.1, data_15_4412.2]

/-- Complete interval computation for depth 15, residue 4413. -/
theorem bounds_15_4413 : exactInterval 15 4413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4413 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4413) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4413 : oddCount 4413 15 = 7 ∧ acceleratedOrbit 15 4413 = 296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4413 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4413) = 3 ^ 7 * m + 296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4413.1, data_15_4413.2]

/-- Complete interval computation for depth 15, residue 4414. -/
theorem bounds_15_4414 : exactInterval 15 4414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4414 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4414) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4414 : oddCount 4414 15 = 12 ∧ acceleratedOrbit 15 4414 = 71624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4414 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4414) = 3 ^ 12 * m + 71624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4414.1, data_15_4414.2]

/-- Complete interval computation for depth 15, residue 4415. -/
theorem bounds_15_4415 : exactInterval 15 4415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4415 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4415) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4415 : oddCount 4415 15 = 12 ∧ acceleratedOrbit 15 4415 = 71624 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4415 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4415) = 3 ^ 12 * m + 71624 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4415.1, data_15_4415.2]

/-- Complete interval computation for depth 15, residue 4416. -/
theorem bounds_15_4416 : exactInterval 15 4416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4416 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4416) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4416 : oddCount 4416 15 = 3 ∧ acceleratedOrbit 15 4416 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4416 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4416) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4416.1, data_15_4416.2]

/-- Complete interval computation for depth 15, residue 4417. -/
theorem bounds_15_4417 : exactInterval 15 4417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4417 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4417) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4417 : oddCount 4417 15 = 8 ∧ acceleratedOrbit 15 4417 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4417 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4417) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4417.1, data_15_4417.2]

/-- Complete interval computation for depth 15, residue 4418. -/
theorem bounds_15_4418 : exactInterval 15 4418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4418 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4418) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4418 : oddCount 4418 15 = 8 ∧ acceleratedOrbit 15 4418 = 886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4418 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4418) = 3 ^ 8 * m + 886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4418.1, data_15_4418.2]

/-- Complete interval computation for depth 15, residue 4419. -/
theorem bounds_15_4419 : exactInterval 15 4419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4419 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4419) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4419 : oddCount 4419 15 = 8 ∧ acceleratedOrbit 15 4419 = 886 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4419 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4419) = 3 ^ 8 * m + 886 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4419.1, data_15_4419.2]

/-- Complete interval computation for depth 15, residue 4420. -/
theorem bounds_15_4420 : exactInterval 15 4420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4420 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4420) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4420 : oddCount 4420 15 = 8 ∧ acceleratedOrbit 15 4420 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4420 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4420) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4420.1, data_15_4420.2]

/-- Complete interval computation for depth 15, residue 4421. -/
theorem bounds_15_4421 : exactInterval 15 4421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4421 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4421) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4421 : oddCount 4421 15 = 8 ∧ acceleratedOrbit 15 4421 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4421 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4421) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4421.1, data_15_4421.2]

/-- Complete interval computation for depth 15, residue 4422. -/
theorem bounds_15_4422 : exactInterval 15 4422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4422 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4422) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4422 : oddCount 4422 15 = 8 ∧ acceleratedOrbit 15 4422 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4422 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4422) = 3 ^ 8 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4422.1, data_15_4422.2]

end Collatz.Research.PassageAtlas.Batch0135
