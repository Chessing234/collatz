import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0495

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 419. -/
theorem bounds_13_419 : exactInterval 13 419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_419 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 419) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_419 : oddCount 419 13 = 6 ∧ acceleratedOrbit 13 419 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_419 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 419) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_419.1, data_13_419.2]

/-- Complete interval computation for depth 13, residue 420. -/
theorem bounds_13_420 : exactInterval 13 420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_420 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 420) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_420 : oddCount 420 13 = 6 ∧ acceleratedOrbit 13 420 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_420 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 420) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_420.1, data_13_420.2]

/-- Complete interval computation for depth 13, residue 421. -/
theorem bounds_13_421 : exactInterval 13 421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_421 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 421) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_421 : oddCount 421 13 = 6 ∧ acceleratedOrbit 13 421 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_421 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 421) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_421.1, data_13_421.2]

/-- Complete interval computation for depth 13, residue 422. -/
theorem bounds_13_422 : exactInterval 13 422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_422 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 422) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_422 : oddCount 422 13 = 6 ∧ acceleratedOrbit 13 422 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_422 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 422) = 3 ^ 6 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_422.1, data_13_422.2]

/-- Complete interval computation for depth 13, residue 423. -/
theorem bounds_13_423 : exactInterval 13 423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_423 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 423) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_423 : oddCount 423 13 = 8 ∧ acceleratedOrbit 13 423 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_423 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 423) = 3 ^ 8 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_423.1, data_13_423.2]

/-- Complete interval computation for depth 13, residue 424. -/
theorem bounds_13_424 : exactInterval 13 424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_424 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 424) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_424 : oddCount 424 13 = 3 ∧ acceleratedOrbit 13 424 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_424 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 424) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_424.1, data_13_424.2]

/-- Complete interval computation for depth 13, residue 425. -/
theorem bounds_13_425 : exactInterval 13 425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_425 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 425) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_425 : oddCount 425 13 = 10 ∧ acceleratedOrbit 13 425 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_425 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 425) = 3 ^ 10 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_425.1, data_13_425.2]

/-- Complete interval computation for depth 13, residue 426. -/
theorem bounds_13_426 : exactInterval 13 426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_426 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 426) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_426 : oddCount 426 13 = 3 ∧ acceleratedOrbit 13 426 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_426 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 426) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_426.1, data_13_426.2]

/-- Complete interval computation for depth 13, residue 427. -/
theorem bounds_13_427 : exactInterval 13 427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_427 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 427) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_427 : oddCount 427 13 = 8 ∧ acceleratedOrbit 13 427 = 344 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_427 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 427) = 3 ^ 8 * m + 344 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_427.1, data_13_427.2]

/-- Complete interval computation for depth 13, residue 428. -/
theorem bounds_13_428 : exactInterval 13 428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_428 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 428) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_428 : oddCount 428 13 = 8 ∧ acceleratedOrbit 13 428 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_428 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 428) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_428.1, data_13_428.2]

/-- Complete interval computation for depth 13, residue 429. -/
theorem bounds_13_429 : exactInterval 13 429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_429 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 429) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_429 : oddCount 429 13 = 8 ∧ acceleratedOrbit 13 429 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_429 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 429) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_429.1, data_13_429.2]

/-- Complete interval computation for depth 13, residue 430. -/
theorem bounds_13_430 : exactInterval 13 430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_430 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 430) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_430 : oddCount 430 13 = 8 ∧ acceleratedOrbit 13 430 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_430 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 430) = 3 ^ 8 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_430.1, data_13_430.2]

/-- Complete interval computation for depth 13, residue 431. -/
theorem bounds_13_431 : exactInterval 13 431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_431 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 431) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_431 : oddCount 431 13 = 7 ∧ acceleratedOrbit 13 431 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_431 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 431) = 3 ^ 7 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_431.1, data_13_431.2]

/-- Complete interval computation for depth 13, residue 432. -/
theorem bounds_13_432 : exactInterval 13 432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_432 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 432) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_432 : oddCount 432 13 = 7 ∧ acceleratedOrbit 13 432 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_432 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 432) = 3 ^ 7 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_432.1, data_13_432.2]

/-- Complete interval computation for depth 13, residue 433. -/
theorem bounds_13_433 : exactInterval 13 433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_433 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 433) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_433 : oddCount 433 13 = 6 ∧ acceleratedOrbit 13 433 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_433 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 433) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_433.1, data_13_433.2]

/-- Complete interval computation for depth 13, residue 434. -/
theorem bounds_13_434 : exactInterval 13 434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_434 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 434) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_434 : oddCount 434 13 = 6 ∧ acceleratedOrbit 13 434 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_434 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 434) = 3 ^ 6 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_434.1, data_13_434.2]

end Collatz.Research.StoppingAtlas.Batch0495
