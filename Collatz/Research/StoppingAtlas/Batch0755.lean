import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0755

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4413. -/
theorem bounds_13_4413 : exactInterval 13 4413 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4413 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4413) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4413 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4413 : oddCount 4413 13 = 5 ∧ acceleratedOrbit 13 4413 = 131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4413 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4413) = 3 ^ 5 * m + 131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4413.1, data_13_4413.2]

/-- Complete interval computation for depth 13, residue 4414. -/
theorem bounds_13_4414 : exactInterval 13 4414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4414 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4414) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4414 : oddCount 4414 13 = 11 ∧ acceleratedOrbit 13 4414 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4414 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4414) = 3 ^ 11 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4414.1, data_13_4414.2]

/-- Complete interval computation for depth 13, residue 4415. -/
theorem bounds_13_4415 : exactInterval 13 4415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4415 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4415) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4415 : oddCount 4415 13 = 11 ∧ acceleratedOrbit 13 4415 = 95498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4415 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4415) = 3 ^ 11 * m + 95498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4415.1, data_13_4415.2]

/-- Complete interval computation for depth 13, residue 4416. -/
theorem bounds_13_4416 : exactInterval 13 4416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4416 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4416) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4416 : oddCount 4416 13 = 2 ∧ acceleratedOrbit 13 4416 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4416 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4416) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4416.1, data_13_4416.2]

/-- Complete interval computation for depth 13, residue 4417. -/
theorem bounds_13_4417 : exactInterval 13 4417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4417 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4417) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4417 : oddCount 4417 13 = 6 ∧ acceleratedOrbit 13 4417 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4417 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4417) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4417.1, data_13_4417.2]

/-- Complete interval computation for depth 13, residue 4418. -/
theorem bounds_13_4418 : exactInterval 13 4418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4418 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4418) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4418 : oddCount 4418 13 = 7 ∧ acceleratedOrbit 13 4418 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4418 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4418) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4418.1, data_13_4418.2]

/-- Complete interval computation for depth 13, residue 4419. -/
theorem bounds_13_4419 : exactInterval 13 4419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4419 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4419) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4419 : oddCount 4419 13 = 7 ∧ acceleratedOrbit 13 4419 = 1181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4419 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4419) = 3 ^ 7 * m + 1181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4419.1, data_13_4419.2]

/-- Complete interval computation for depth 13, residue 4420. -/
theorem bounds_13_4420 : exactInterval 13 4420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4420 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4420) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4420 : oddCount 4420 13 = 6 ∧ acceleratedOrbit 13 4420 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4420 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4420) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4420.1, data_13_4420.2]

/-- Complete interval computation for depth 13, residue 4421. -/
theorem bounds_13_4421 : exactInterval 13 4421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4421 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4421) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4421 : oddCount 4421 13 = 6 ∧ acceleratedOrbit 13 4421 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4421 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4421) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4421.1, data_13_4421.2]

/-- Complete interval computation for depth 13, residue 4422. -/
theorem bounds_13_4422 : exactInterval 13 4422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4422 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4422) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4422 : oddCount 4422 13 = 6 ∧ acceleratedOrbit 13 4422 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4422 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4422) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4422.1, data_13_4422.2]

/-- Complete interval computation for depth 13, residue 4423. -/
theorem bounds_13_4423 : exactInterval 13 4423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4423 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4423) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4423 : oddCount 4423 13 = 9 ∧ acceleratedOrbit 13 4423 = 10631 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4423 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4423) = 3 ^ 9 * m + 10631 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4423.1, data_13_4423.2]

/-- Complete interval computation for depth 13, residue 4424. -/
theorem bounds_13_4424 : exactInterval 13 4424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4424 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4424) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4424 : oddCount 4424 13 = 8 ∧ acceleratedOrbit 13 4424 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4424 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4424) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4424.1, data_13_4424.2]

/-- Complete interval computation for depth 13, residue 4425. -/
theorem bounds_13_4425 : exactInterval 13 4425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4425 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4425) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4425 : oddCount 4425 13 = 6 ∧ acceleratedOrbit 13 4425 = 394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4425 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4425) = 3 ^ 6 * m + 394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4425.1, data_13_4425.2]

/-- Complete interval computation for depth 13, residue 4426. -/
theorem bounds_13_4426 : exactInterval 13 4426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4426 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4426) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4426 : oddCount 4426 13 = 8 ∧ acceleratedOrbit 13 4426 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4426 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4426) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4426.1, data_13_4426.2]

/-- Complete interval computation for depth 13, residue 4427. -/
theorem bounds_13_4427 : exactInterval 13 4427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4427 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4427) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4427 : oddCount 4427 13 = 6 ∧ acceleratedOrbit 13 4427 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4427 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4427) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4427.1, data_13_4427.2]

end Collatz.Research.StoppingAtlas.Batch0755
