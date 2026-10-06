import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0228

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 414. -/
theorem bounds_12_414 : exactInterval 12 414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_414 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 414) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_414 : oddCount 414 12 = 8 ∧ acceleratedOrbit 12 414 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_414 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 414) = 3 ^ 8 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_414.1, data_12_414.2]

/-- Complete interval computation for depth 12, residue 415. -/
theorem bounds_12_415 : exactInterval 12 415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_415 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 415) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_415 : oddCount 415 12 = 9 ∧ acceleratedOrbit 12 415 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_415 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 415) = 3 ^ 9 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_415.1, data_12_415.2]

/-- Complete interval computation for depth 12, residue 416. -/
theorem bounds_12_416 : exactInterval 12 416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_416 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 416) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_416 : oddCount 416 12 = 2 ∧ acceleratedOrbit 12 416 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_416 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 416) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_416.1, data_12_416.2]

/-- Complete interval computation for depth 12, residue 417. -/
theorem bounds_12_417 : exactInterval 12 417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_417 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 417) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_417 : oddCount 417 12 = 8 ∧ acceleratedOrbit 12 417 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_417 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 417) = 3 ^ 8 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_417.1, data_12_417.2]

/-- Complete interval computation for depth 12, residue 418. -/
theorem bounds_12_418 : exactInterval 12 418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_418 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 418) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_418 : oddCount 418 12 = 6 ∧ acceleratedOrbit 12 418 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_418 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 418) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_418.1, data_12_418.2]

/-- Complete interval computation for depth 12, residue 419. -/
theorem bounds_12_419 : exactInterval 12 419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_419 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 419) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_419 : oddCount 419 12 = 6 ∧ acceleratedOrbit 12 419 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_419 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 419) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_419.1, data_12_419.2]

/-- Complete interval computation for depth 12, residue 420. -/
theorem bounds_12_420 : exactInterval 12 420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_420 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 420) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_420 : oddCount 420 12 = 6 ∧ acceleratedOrbit 12 420 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_420 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 420) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_420.1, data_12_420.2]

/-- Complete interval computation for depth 12, residue 421. -/
theorem bounds_12_421 : exactInterval 12 421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_421 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 421) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_421 : oddCount 421 12 = 6 ∧ acceleratedOrbit 12 421 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_421 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 421) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_421.1, data_12_421.2]

/-- Complete interval computation for depth 12, residue 422. -/
theorem bounds_12_422 : exactInterval 12 422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_422 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 422) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_422 : oddCount 422 12 = 6 ∧ acceleratedOrbit 12 422 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_422 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 422) = 3 ^ 6 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_422.1, data_12_422.2]

/-- Complete interval computation for depth 12, residue 423. -/
theorem bounds_12_423 : exactInterval 12 423 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_423 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 423) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_423 : oddCount 423 12 = 7 ∧ acceleratedOrbit 12 423 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_423 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 423) = 3 ^ 7 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_423.1, data_12_423.2]

/-- Complete interval computation for depth 12, residue 424. -/
theorem bounds_12_424 : exactInterval 12 424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_424 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 424) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_424 : oddCount 424 12 = 2 ∧ acceleratedOrbit 12 424 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_424 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 424) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_424.1, data_12_424.2]

/-- Complete interval computation for depth 12, residue 425. -/
theorem bounds_12_425 : exactInterval 12 425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_425 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 425) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_425 : oddCount 425 12 = 9 ∧ acceleratedOrbit 12 425 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_425 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 425) = 3 ^ 9 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_425.1, data_12_425.2]

/-- Complete interval computation for depth 12, residue 426. -/
theorem bounds_12_426 : exactInterval 12 426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_426 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 426) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_426 : oddCount 426 12 = 2 ∧ acceleratedOrbit 12 426 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_426 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 426) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_426.1, data_12_426.2]

/-- Complete interval computation for depth 12, residue 427. -/
theorem bounds_12_427 : exactInterval 12 427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_427 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 427) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_427 : oddCount 427 12 = 8 ∧ acceleratedOrbit 12 427 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_427 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 427) = 3 ^ 8 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_427.1, data_12_427.2]

/-- Complete interval computation for depth 12, residue 428. -/
theorem bounds_12_428 : exactInterval 12 428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_428 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 428) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_428 : oddCount 428 12 = 7 ∧ acceleratedOrbit 12 428 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_428 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 428) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_428.1, data_12_428.2]

/-- Complete interval computation for depth 12, residue 429. -/
theorem bounds_12_429 : exactInterval 12 429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_429 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 429) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_429 : oddCount 429 12 = 7 ∧ acceleratedOrbit 12 429 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_429 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 429) = 3 ^ 7 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_429.1, data_12_429.2]

end Collatz.Research.StoppingAtlas.Batch0228
