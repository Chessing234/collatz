import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0028

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 414. -/
theorem bounds_10_414 : exactInterval 10 414 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_414 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 414) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_414 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_414 : oddCount 414 10 = 7 ∧ acceleratedOrbit 10 414 = 890 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_414 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 414) = 3 ^ 7 * m + 890 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_414.1, data_10_414.2]

/-- Complete interval computation for depth 10, residue 415. -/
theorem bounds_10_415 : exactInterval 10 415 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_415 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 415) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_415 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_415 : oddCount 415 10 = 8 ∧ acceleratedOrbit 10 415 = 2666 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_415 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 415) = 3 ^ 8 * m + 2666 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_415.1, data_10_415.2]

/-- Complete interval computation for depth 10, residue 416. -/
theorem bounds_10_416 : exactInterval 10 416 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_416 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 416) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_416 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_416 : oddCount 416 10 = 2 ∧ acceleratedOrbit 10 416 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_416 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 416) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_416.1, data_10_416.2]

/-- Complete interval computation for depth 10, residue 417. -/
theorem bounds_10_417 : exactInterval 10 417 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_417 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 417) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_417 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_417 : oddCount 417 10 = 6 ∧ acceleratedOrbit 10 417 = 299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_417 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 417) = 3 ^ 6 * m + 299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_417.1, data_10_417.2]

/-- Complete interval computation for depth 10, residue 418. -/
theorem bounds_10_418 : exactInterval 10 418 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_418 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 418) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_418 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_418 : oddCount 418 10 = 5 ∧ acceleratedOrbit 10 418 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_418 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 418) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_418.1, data_10_418.2]

/-- Complete interval computation for depth 10, residue 419. -/
theorem bounds_10_419 : exactInterval 10 419 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_419 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 419) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_419 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_419 : oddCount 419 10 = 5 ∧ acceleratedOrbit 10 419 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_419 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 419) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_419.1, data_10_419.2]

/-- Complete interval computation for depth 10, residue 420. -/
theorem bounds_10_420 : exactInterval 10 420 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_420 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 420) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_420 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_420 : oddCount 420 10 = 5 ∧ acceleratedOrbit 10 420 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_420 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 420) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_420.1, data_10_420.2]

/-- Complete interval computation for depth 10, residue 421. -/
theorem bounds_10_421 : exactInterval 10 421 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_421 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 421) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_421 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_421 : oddCount 421 10 = 5 ∧ acceleratedOrbit 10 421 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_421 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 421) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_421.1, data_10_421.2]

/-- Complete interval computation for depth 10, residue 422. -/
theorem bounds_10_422 : exactInterval 10 422 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_422 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 422) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_422 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_422 : oddCount 422 10 = 5 ∧ acceleratedOrbit 10 422 = 101 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_422 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 422) = 3 ^ 5 * m + 101 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_422.1, data_10_422.2]

/-- Complete interval computation for depth 10, residue 423. -/
theorem bounds_10_423 : exactInterval 10 423 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_423 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 423) 10 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_423 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_423 : oddCount 423 10 = 6 ∧ acceleratedOrbit 10 423 = 302 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_423 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 423) = 3 ^ 6 * m + 302 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_423.1, data_10_423.2]

/-- Complete interval computation for depth 10, residue 424. -/
theorem bounds_10_424 : exactInterval 10 424 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_424 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 424) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_424 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_424 : oddCount 424 10 = 2 ∧ acceleratedOrbit 10 424 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_424 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 424) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_424.1, data_10_424.2]

/-- Complete interval computation for depth 10, residue 425. -/
theorem bounds_10_425 : exactInterval 10 425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_425 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 425) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_425 : oddCount 425 10 = 7 ∧ acceleratedOrbit 10 425 = 911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_425 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 425) = 3 ^ 7 * m + 911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_425.1, data_10_425.2]

/-- Complete interval computation for depth 10, residue 426. -/
theorem bounds_10_426 : exactInterval 10 426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_426 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 426) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_426 : oddCount 426 10 = 2 ∧ acceleratedOrbit 10 426 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_426 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 426) = 3 ^ 2 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_426.1, data_10_426.2]

/-- Complete interval computation for depth 10, residue 427. -/
theorem bounds_10_427 : exactInterval 10 427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_427 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 427) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_427 : oddCount 427 10 = 7 ∧ acceleratedOrbit 10 427 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_427 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 427) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_427.1, data_10_427.2]

/-- Complete interval computation for depth 10, residue 428. -/
theorem bounds_10_428 : exactInterval 10 428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_428 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 428) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_428 : oddCount 428 10 = 5 ∧ acceleratedOrbit 10 428 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_428 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 428) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_428.1, data_10_428.2]

/-- Complete interval computation for depth 10, residue 429. -/
theorem bounds_10_429 : exactInterval 10 429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_429 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 429) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_429 : oddCount 429 10 = 5 ∧ acceleratedOrbit 10 429 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_429 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 429) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_429.1, data_10_429.2]

end Collatz.Research.StoppingAtlas.Batch0028
