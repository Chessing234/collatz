import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0754

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4398. -/
theorem bounds_13_4398 : exactInterval 13 4398 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4398 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4398) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4398 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4398 : oddCount 4398 13 = 4 ∧ acceleratedOrbit 13 4398 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4398 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4398) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4398.1, data_13_4398.2]

/-- Complete interval computation for depth 13, residue 4399. -/
theorem bounds_13_4399 : exactInterval 13 4399 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4399 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4399) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4399 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4399 : oddCount 4399 13 = 9 ∧ acceleratedOrbit 13 4399 = 10574 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4399 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4399) = 3 ^ 9 * m + 10574 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4399.1, data_13_4399.2]

/-- Complete interval computation for depth 13, residue 4400. -/
theorem bounds_13_4400 : exactInterval 13 4400 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4400 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4400) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4400 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4400 : oddCount 4400 13 = 6 ∧ acceleratedOrbit 13 4400 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4400 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4400) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4400.1, data_13_4400.2]

/-- Complete interval computation for depth 13, residue 4401. -/
theorem bounds_13_4401 : exactInterval 13 4401 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4401 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4401) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4401 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4401 : oddCount 4401 13 = 7 ∧ acceleratedOrbit 13 4401 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4401 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4401) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4401.1, data_13_4401.2]

/-- Complete interval computation for depth 13, residue 4402. -/
theorem bounds_13_4402 : exactInterval 13 4402 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4402 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4402) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4402 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4402 : oddCount 4402 13 = 7 ∧ acceleratedOrbit 13 4402 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4402 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4402) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4402.1, data_13_4402.2]

/-- Complete interval computation for depth 13, residue 4403. -/
theorem bounds_13_4403 : exactInterval 13 4403 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4403 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4403) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4403 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4403 : oddCount 4403 13 = 7 ∧ acceleratedOrbit 13 4403 = 1178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4403 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4403) = 3 ^ 7 * m + 1178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4403.1, data_13_4403.2]

/-- Complete interval computation for depth 13, residue 4404. -/
theorem bounds_13_4404 : exactInterval 13 4404 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4404 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4404) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4404 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4404 : oddCount 4404 13 = 6 ∧ acceleratedOrbit 13 4404 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4404 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4404) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4404.1, data_13_4404.2]

/-- Complete interval computation for depth 13, residue 4405. -/
theorem bounds_13_4405 : exactInterval 13 4405 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4405 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4405) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4405 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4405 : oddCount 4405 13 = 6 ∧ acceleratedOrbit 13 4405 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4405 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4405) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4405.1, data_13_4405.2]

/-- Complete interval computation for depth 13, residue 4406. -/
theorem bounds_13_4406 : exactInterval 13 4406 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4406 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4406) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4406 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4406 : oddCount 4406 13 = 7 ∧ acceleratedOrbit 13 4406 = 1177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4406 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4406) = 3 ^ 7 * m + 1177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4406.1, data_13_4406.2]

/-- Complete interval computation for depth 13, residue 4407. -/
theorem bounds_13_4407 : exactInterval 13 4407 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4407 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4407) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4407 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4407 : oddCount 4407 13 = 7 ∧ acceleratedOrbit 13 4407 = 1177 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4407 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4407) = 3 ^ 7 * m + 1177 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4407.1, data_13_4407.2]

/-- Complete interval computation for depth 13, residue 4408. -/
theorem bounds_13_4408 : exactInterval 13 4408 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4408 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4408) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4408 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4408 : oddCount 4408 13 = 5 ∧ acceleratedOrbit 13 4408 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4408 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4408) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4408.1, data_13_4408.2]

/-- Complete interval computation for depth 13, residue 4409. -/
theorem bounds_13_4409 : exactInterval 13 4409 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4409 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4409) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4409 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4409 : oddCount 4409 13 = 9 ∧ acceleratedOrbit 13 4409 = 10601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4409 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4409) = 3 ^ 9 * m + 10601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4409.1, data_13_4409.2]

/-- Complete interval computation for depth 13, residue 4410. -/
theorem bounds_13_4410 : exactInterval 13 4410 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4410 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4410) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4410 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4410 : oddCount 4410 13 = 5 ∧ acceleratedOrbit 13 4410 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4410 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4410) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4410.1, data_13_4410.2]

/-- Complete interval computation for depth 13, residue 4411. -/
theorem bounds_13_4411 : exactInterval 13 4411 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4411 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4411) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4411 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4411 : oddCount 4411 13 = 5 ∧ acceleratedOrbit 13 4411 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4411 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4411) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4411.1, data_13_4411.2]

/-- Complete interval computation for depth 13, residue 4412. -/
theorem bounds_13_4412 : exactInterval 13 4412 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4412 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4412) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4412 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4412 : oddCount 4412 13 = 5 ∧ acceleratedOrbit 13 4412 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4412 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4412) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4412.1, data_13_4412.2]

end Collatz.Research.StoppingAtlas.Batch0754
