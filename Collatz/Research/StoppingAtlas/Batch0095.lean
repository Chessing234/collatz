import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0095

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 419. -/
theorem bounds_11_419 : exactInterval 11 419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_419 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 419) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_419 : oddCount 419 11 = 6 ∧ acceleratedOrbit 11 419 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_419 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 419) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_419.1, data_11_419.2]

/-- Complete interval computation for depth 11, residue 420. -/
theorem bounds_11_420 : exactInterval 11 420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_420 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 420) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_420 : oddCount 420 11 = 6 ∧ acceleratedOrbit 11 420 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_420 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 420) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_420.1, data_11_420.2]

/-- Complete interval computation for depth 11, residue 421. -/
theorem bounds_11_421 : exactInterval 11 421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_421 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 421) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_421 : oddCount 421 11 = 6 ∧ acceleratedOrbit 11 421 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_421 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 421) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_421.1, data_11_421.2]

/-- Complete interval computation for depth 11, residue 422. -/
theorem bounds_11_422 : exactInterval 11 422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_422 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 422) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_422 : oddCount 422 11 = 6 ∧ acceleratedOrbit 11 422 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_422 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 422) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_422.1, data_11_422.2]

/-- Complete interval computation for depth 11, residue 423. -/
theorem bounds_11_423 : exactInterval 11 423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_423 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 423) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_423 : oddCount 423 11 = 6 ∧ acceleratedOrbit 11 423 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_423 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 423) = 3 ^ 6 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_423.1, data_11_423.2]

/-- Complete interval computation for depth 11, residue 424. -/
theorem bounds_11_424 : exactInterval 11 424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_424 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 424) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_424 : oddCount 424 11 = 2 ∧ acceleratedOrbit 11 424 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_424 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 424) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_424.1, data_11_424.2]

/-- Complete interval computation for depth 11, residue 425. -/
theorem bounds_11_425 : exactInterval 11 425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_425 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 425) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_425 : oddCount 425 11 = 8 ∧ acceleratedOrbit 11 425 = 1367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_425 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 425) = 3 ^ 8 * m + 1367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_425.1, data_11_425.2]

/-- Complete interval computation for depth 11, residue 426. -/
theorem bounds_11_426 : exactInterval 11 426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_426 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 426) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_426 : oddCount 426 11 = 2 ∧ acceleratedOrbit 11 426 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_426 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 426) = 3 ^ 2 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_426.1, data_11_426.2]

/-- Complete interval computation for depth 11, residue 427. -/
theorem bounds_11_427 : exactInterval 11 427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_427 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 427) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_427 : oddCount 427 11 = 8 ∧ acceleratedOrbit 11 427 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_427 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 427) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_427.1, data_11_427.2]

/-- Complete interval computation for depth 11, residue 428. -/
theorem bounds_11_428 : exactInterval 11 428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_428 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 428) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_428 : oddCount 428 11 = 6 ∧ acceleratedOrbit 11 428 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_428 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 428) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_428.1, data_11_428.2]

/-- Complete interval computation for depth 11, residue 429. -/
theorem bounds_11_429 : exactInterval 11 429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_429 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 429) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_429 : oddCount 429 11 = 6 ∧ acceleratedOrbit 11 429 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_429 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 429) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_429.1, data_11_429.2]

/-- Complete interval computation for depth 11, residue 430. -/
theorem bounds_11_430 : exactInterval 11 430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_430 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 430) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_430 : oddCount 430 11 = 6 ∧ acceleratedOrbit 11 430 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_430 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 430) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_430.1, data_11_430.2]

/-- Complete interval computation for depth 11, residue 431. -/
theorem bounds_11_431 : exactInterval 11 431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_431 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 431) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_431 : oddCount 431 11 = 6 ∧ acceleratedOrbit 11 431 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_431 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 431) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_431.1, data_11_431.2]

/-- Complete interval computation for depth 11, residue 432. -/
theorem bounds_11_432 : exactInterval 11 432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_432 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 432) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_432 : oddCount 432 11 = 6 ∧ acceleratedOrbit 11 432 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_432 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 432) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_432.1, data_11_432.2]

/-- Complete interval computation for depth 11, residue 433. -/
theorem bounds_11_433 : exactInterval 11 433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_433 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 433) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_433 : oddCount 433 11 = 5 ∧ acceleratedOrbit 11 433 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_433 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 433) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_433.1, data_11_433.2]

/-- Complete interval computation for depth 11, residue 434. -/
theorem bounds_11_434 : exactInterval 11 434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_434 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 434) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_434 : oddCount 434 11 = 5 ∧ acceleratedOrbit 11 434 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_434 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 434) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_434.1, data_11_434.2]

end Collatz.Research.StoppingAtlas.Batch0095
