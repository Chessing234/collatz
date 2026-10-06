import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0014

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 425. -/
theorem bounds_15_425 : exactInterval 15 425 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_425 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 425) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_425 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_425 : oddCount 425 15 = 11 ∧ acceleratedOrbit 15 425 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_425 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 425) = 3 ^ 11 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_425.1, data_15_425.2]

/-- Complete interval computation for depth 15, residue 426. -/
theorem bounds_15_426 : exactInterval 15 426 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_426 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 426) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_426 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_426 : oddCount 426 15 = 4 ∧ acceleratedOrbit 15 426 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_426 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 426) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_426.1, data_15_426.2]

/-- Complete interval computation for depth 15, residue 427. -/
theorem bounds_15_427 : exactInterval 15 427 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_427 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 427) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_427 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_427 : oddCount 427 15 = 8 ∧ acceleratedOrbit 15 427 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_427 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 427) = 3 ^ 8 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_427.1, data_15_427.2]

/-- Complete interval computation for depth 15, residue 428. -/
theorem bounds_15_428 : exactInterval 15 428 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_428 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 428) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_428 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_428 : oddCount 428 15 = 9 ∧ acceleratedOrbit 15 428 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_428 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 428) = 3 ^ 9 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_428.1, data_15_428.2]

/-- Complete interval computation for depth 15, residue 429. -/
theorem bounds_15_429 : exactInterval 15 429 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_429 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 429) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_429 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_429 : oddCount 429 15 = 9 ∧ acceleratedOrbit 15 429 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_429 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 429) = 3 ^ 9 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_429.1, data_15_429.2]

/-- Complete interval computation for depth 15, residue 430. -/
theorem bounds_15_430 : exactInterval 15 430 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_430 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 430) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_430 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_430 : oddCount 430 15 = 9 ∧ acceleratedOrbit 15 430 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_430 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 430) = 3 ^ 9 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_430.1, data_15_430.2]

/-- Complete interval computation for depth 15, residue 431. -/
theorem bounds_15_431 : exactInterval 15 431 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_431 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 431) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_431 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_431 : oddCount 431 15 = 7 ∧ acceleratedOrbit 15 431 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_431 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 431) = 3 ^ 7 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_431.1, data_15_431.2]

/-- Complete interval computation for depth 15, residue 432. -/
theorem bounds_15_432 : exactInterval 15 432 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_432 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 432) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_432 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_432 : oddCount 432 15 = 8 ∧ acceleratedOrbit 15 432 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_432 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 432) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_432.1, data_15_432.2]

/-- Complete interval computation for depth 15, residue 433. -/
theorem bounds_15_433 : exactInterval 15 433 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_433 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 433) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_433 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_433 : oddCount 433 15 = 6 ∧ acceleratedOrbit 15 433 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_433 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 433) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_433.1, data_15_433.2]

/-- Complete interval computation for depth 15, residue 434. -/
theorem bounds_15_434 : exactInterval 15 434 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_434 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 434) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_434 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_434 : oddCount 434 15 = 6 ∧ acceleratedOrbit 15 434 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_434 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 434) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_434.1, data_15_434.2]

/-- Complete interval computation for depth 15, residue 435. -/
theorem bounds_15_435 : exactInterval 15 435 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_435 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 435) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_435 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_435 : oddCount 435 15 = 6 ∧ acceleratedOrbit 15 435 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_435 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 435) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_435.1, data_15_435.2]

/-- Complete interval computation for depth 15, residue 436. -/
theorem bounds_15_436 : exactInterval 15 436 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_436 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 436) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_436 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_436 : oddCount 436 15 = 8 ∧ acceleratedOrbit 15 436 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_436 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 436) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_436.1, data_15_436.2]

/-- Complete interval computation for depth 15, residue 437. -/
theorem bounds_15_437 : exactInterval 15 437 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_437 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 437) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_437 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_437 : oddCount 437 15 = 8 ∧ acceleratedOrbit 15 437 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_437 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 437) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_437.1, data_15_437.2]

/-- Complete interval computation for depth 15, residue 438. -/
theorem bounds_15_438 : exactInterval 15 438 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_438 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 438) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_438 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_438 : oddCount 438 15 = 8 ∧ acceleratedOrbit 15 438 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_438 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 438) = 3 ^ 8 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_438.1, data_15_438.2]

/-- Complete interval computation for depth 15, residue 439. -/
theorem bounds_15_439 : exactInterval 15 439 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_439 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 439) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_439 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_439 : oddCount 439 15 = 8 ∧ acceleratedOrbit 15 439 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_439 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 439) = 3 ^ 8 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_439.1, data_15_439.2]

/-- Complete interval computation for depth 15, residue 440. -/
theorem bounds_15_440 : exactInterval 15 440 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_440 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 440) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_440 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_440 : oddCount 440 15 = 8 ∧ acceleratedOrbit 15 440 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_440 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 440) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_440.1, data_15_440.2]

/-- Complete interval computation for depth 15, residue 441. -/
theorem bounds_15_441 : exactInterval 15 441 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_441 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 441) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_441 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_441 : oddCount 441 15 = 6 ∧ acceleratedOrbit 15 441 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_441 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 441) = 3 ^ 6 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_441.1, data_15_441.2]

/-- Complete interval computation for depth 15, residue 442. -/
theorem bounds_15_442 : exactInterval 15 442 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_442 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 442) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_442 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_442 : oddCount 442 15 = 8 ∧ acceleratedOrbit 15 442 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_442 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 442) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_442.1, data_15_442.2]

/-- Complete interval computation for depth 15, residue 443. -/
theorem bounds_15_443 : exactInterval 15 443 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_443 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 443) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_443 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_443 : oddCount 443 15 = 9 ∧ acceleratedOrbit 15 443 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_443 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 443) = 3 ^ 9 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_443.1, data_15_443.2]

/-- Complete interval computation for depth 15, residue 444. -/
theorem bounds_15_444 : exactInterval 15 444 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_444 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 444) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_444 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_444 : oddCount 444 15 = 11 ∧ acceleratedOrbit 15 444 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_444 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 444) = 3 ^ 11 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_444.1, data_15_444.2]

/-- Complete interval computation for depth 15, residue 445. -/
theorem bounds_15_445 : exactInterval 15 445 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_445 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 445) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_445 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_445 : oddCount 445 15 = 11 ∧ acceleratedOrbit 15 445 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_445 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 445) = 3 ^ 11 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_445.1, data_15_445.2]

/-- Complete interval computation for depth 15, residue 446. -/
theorem bounds_15_446 : exactInterval 15 446 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_446 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 446) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_446 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_446 : oddCount 446 15 = 11 ∧ acceleratedOrbit 15 446 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_446 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 446) = 3 ^ 11 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_446.1, data_15_446.2]

/-- Complete interval computation for depth 15, residue 447. -/
theorem bounds_15_447 : exactInterval 15 447 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_447 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 447) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_447 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_447 : oddCount 447 15 = 11 ∧ acceleratedOrbit 15 447 = 2423 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_447 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 447) = 3 ^ 11 * m + 2423 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_447.1, data_15_447.2]

/-- Complete interval computation for depth 15, residue 448. -/
theorem bounds_15_448 : exactInterval 15 448 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_448 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 448) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_448 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_448 : oddCount 448 15 = 5 ∧ acceleratedOrbit 15 448 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_448 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 448) = 3 ^ 5 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_448.1, data_15_448.2]

/-- Complete interval computation for depth 15, residue 449. -/
theorem bounds_15_449 : exactInterval 15 449 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_449 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 449) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_449 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_449 : oddCount 449 15 = 8 ∧ acceleratedOrbit 15 449 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_449 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 449) = 3 ^ 8 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_449.1, data_15_449.2]

/-- Complete interval computation for depth 15, residue 450. -/
theorem bounds_15_450 : exactInterval 15 450 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_450 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 450) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_450 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_450 : oddCount 450 15 = 10 ∧ acceleratedOrbit 15 450 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_450 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 450) = 3 ^ 10 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_450.1, data_15_450.2]

/-- Complete interval computation for depth 15, residue 451. -/
theorem bounds_15_451 : exactInterval 15 451 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_451 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 451) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_451 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_451 : oddCount 451 15 = 10 ∧ acceleratedOrbit 15 451 = 820 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_451 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 451) = 3 ^ 10 * m + 820 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_451.1, data_15_451.2]

/-- Complete interval computation for depth 15, residue 452. -/
theorem bounds_15_452 : exactInterval 15 452 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_452 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 452) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_452 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_452 : oddCount 452 15 = 4 ∧ acceleratedOrbit 15 452 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_452 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 452) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_452.1, data_15_452.2]

/-- Complete interval computation for depth 15, residue 453. -/
theorem bounds_15_453 : exactInterval 15 453 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_453 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 453) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_453 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_453 : oddCount 453 15 = 4 ∧ acceleratedOrbit 15 453 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_453 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 453) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_453.1, data_15_453.2]

/-- Complete interval computation for depth 15, residue 454. -/
theorem bounds_15_454 : exactInterval 15 454 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_454 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 454) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_454 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_454 : oddCount 454 15 = 4 ∧ acceleratedOrbit 15 454 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_454 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 454) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_454.1, data_15_454.2]

/-- Complete interval computation for depth 15, residue 455. -/
theorem bounds_15_455 : exactInterval 15 455 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_455 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 455) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_455 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_455 : oddCount 455 15 = 8 ∧ acceleratedOrbit 15 455 = 92 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_455 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 455) = 3 ^ 8 * m + 92 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_455.1, data_15_455.2]

/-- Complete interval computation for depth 15, residue 456. -/
theorem bounds_15_456 : exactInterval 15 456 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_456 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 456) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_456 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_456 : oddCount 456 15 = 6 ∧ acceleratedOrbit 15 456 = 11 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_456 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 456) = 3 ^ 6 * m + 11 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_456.1, data_15_456.2]

/-- Complete interval computation for depth 15, residue 457. -/
theorem bounds_15_457 : exactInterval 15 457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_457 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 457) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_457 : oddCount 457 15 = 7 ∧ acceleratedOrbit 15 457 = 31 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_457 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 457) = 3 ^ 7 * m + 31 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_457.1, data_15_457.2]

end Collatz.Research.PassageAtlas.Batch0014
