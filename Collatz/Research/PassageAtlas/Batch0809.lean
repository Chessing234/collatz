import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0809

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26476. -/
theorem bounds_15_26476 : exactInterval 15 26476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26476 : oddCount 26476 15 = 7 ∧ acceleratedOrbit 15 26476 = 1768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26476) = 3 ^ 7 * m + 1768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26476.1, data_15_26476.2]

/-- Complete interval computation for depth 15, residue 26477. -/
theorem bounds_15_26477 : exactInterval 15 26477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26477 : oddCount 26477 15 = 7 ∧ acceleratedOrbit 15 26477 = 1768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26477) = 3 ^ 7 * m + 1768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26477.1, data_15_26477.2]

/-- Complete interval computation for depth 15, residue 26478. -/
theorem bounds_15_26478 : exactInterval 15 26478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26478 : oddCount 26478 15 = 7 ∧ acceleratedOrbit 15 26478 = 1768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26478) = 3 ^ 7 * m + 1768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26478.1, data_15_26478.2]

/-- Complete interval computation for depth 15, residue 26479. -/
theorem bounds_15_26479 : exactInterval 15 26479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26479 : oddCount 26479 15 = 10 ∧ acceleratedOrbit 15 26479 = 47719 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26479) = 3 ^ 10 * m + 47719 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26479.1, data_15_26479.2]

/-- Complete interval computation for depth 15, residue 26480. -/
theorem bounds_15_26480 : exactInterval 15 26480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26480 : oddCount 26480 15 = 5 ∧ acceleratedOrbit 15 26480 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26480) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26480.1, data_15_26480.2]

/-- Complete interval computation for depth 15, residue 26481. -/
theorem bounds_15_26481 : exactInterval 15 26481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26481 : oddCount 26481 15 = 5 ∧ acceleratedOrbit 15 26481 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26481) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26481.1, data_15_26481.2]

/-- Complete interval computation for depth 15, residue 26482. -/
theorem bounds_15_26482 : exactInterval 15 26482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26482 : oddCount 26482 15 = 8 ∧ acceleratedOrbit 15 26482 = 5305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26482) = 3 ^ 8 * m + 5305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26482.1, data_15_26482.2]

/-- Complete interval computation for depth 15, residue 26483. -/
theorem bounds_15_26483 : exactInterval 15 26483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26483 : oddCount 26483 15 = 8 ∧ acceleratedOrbit 15 26483 = 5305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26483) = 3 ^ 8 * m + 5305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26483.1, data_15_26483.2]

/-- Complete interval computation for depth 15, residue 26484. -/
theorem bounds_15_26484 : exactInterval 15 26484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26484 : oddCount 26484 15 = 5 ∧ acceleratedOrbit 15 26484 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26484) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26484.1, data_15_26484.2]

/-- Complete interval computation for depth 15, residue 26485. -/
theorem bounds_15_26485 : exactInterval 15 26485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26485 : oddCount 26485 15 = 5 ∧ acceleratedOrbit 15 26485 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26485) = 3 ^ 5 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26485.1, data_15_26485.2]

/-- Complete interval computation for depth 15, residue 26486. -/
theorem bounds_15_26486 : exactInterval 15 26486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26486 : oddCount 26486 15 = 8 ∧ acceleratedOrbit 15 26486 = 5305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26486) = 3 ^ 8 * m + 5305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26486.1, data_15_26486.2]

/-- Complete interval computation for depth 15, residue 26487. -/
theorem bounds_15_26487 : exactInterval 15 26487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26487 : oddCount 26487 15 = 8 ∧ acceleratedOrbit 15 26487 = 5305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26487) = 3 ^ 8 * m + 5305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26487.1, data_15_26487.2]

/-- Complete interval computation for depth 15, residue 26488. -/
theorem bounds_15_26488 : exactInterval 15 26488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26488 : oddCount 26488 15 = 10 ∧ acceleratedOrbit 15 26488 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26488) = 3 ^ 10 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26488.1, data_15_26488.2]

/-- Complete interval computation for depth 15, residue 26489. -/
theorem bounds_15_26489 : exactInterval 15 26489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26489 : oddCount 26489 15 = 9 ∧ acceleratedOrbit 15 26489 = 15913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26489) = 3 ^ 9 * m + 15913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26489.1, data_15_26489.2]

/-- Complete interval computation for depth 15, residue 26490. -/
theorem bounds_15_26490 : exactInterval 15 26490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26490 : oddCount 26490 15 = 10 ∧ acceleratedOrbit 15 26490 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26490) = 3 ^ 10 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26490.1, data_15_26490.2]

/-- Complete interval computation for depth 15, residue 26491. -/
theorem bounds_15_26491 : exactInterval 15 26491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26491 : oddCount 26491 15 = 9 ∧ acceleratedOrbit 15 26491 = 15914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26491) = 3 ^ 9 * m + 15914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26491.1, data_15_26491.2]

/-- Complete interval computation for depth 15, residue 26492. -/
theorem bounds_15_26492 : exactInterval 15 26492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26492 : oddCount 26492 15 = 10 ∧ acceleratedOrbit 15 26492 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26492) = 3 ^ 10 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26492.1, data_15_26492.2]

/-- Complete interval computation for depth 15, residue 26493. -/
theorem bounds_15_26493 : exactInterval 15 26493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26493 : oddCount 26493 15 = 10 ∧ acceleratedOrbit 15 26493 = 47749 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26493) = 3 ^ 10 * m + 47749 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26493.1, data_15_26493.2]

/-- Complete interval computation for depth 15, residue 26494. -/
theorem bounds_15_26494 : exactInterval 15 26494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26494 : oddCount 26494 15 = 10 ∧ acceleratedOrbit 15 26494 = 47747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26494) = 3 ^ 10 * m + 47747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26494.1, data_15_26494.2]

/-- Complete interval computation for depth 15, residue 26495. -/
theorem bounds_15_26495 : exactInterval 15 26495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26495 : oddCount 26495 15 = 10 ∧ acceleratedOrbit 15 26495 = 47747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26495) = 3 ^ 10 * m + 47747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26495.1, data_15_26495.2]

/-- Complete interval computation for depth 15, residue 26496. -/
theorem bounds_15_26496 : exactInterval 15 26496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26496 : oddCount 26496 15 = 6 ∧ acceleratedOrbit 15 26496 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26496) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26496.1, data_15_26496.2]

/-- Complete interval computation for depth 15, residue 26497. -/
theorem bounds_15_26497 : exactInterval 15 26497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26497 : oddCount 26497 15 = 9 ∧ acceleratedOrbit 15 26497 = 15920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26497) = 3 ^ 9 * m + 15920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26497.1, data_15_26497.2]

/-- Complete interval computation for depth 15, residue 26498. -/
theorem bounds_15_26498 : exactInterval 15 26498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26498 : oddCount 26498 15 = 8 ∧ acceleratedOrbit 15 26498 = 5309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26498) = 3 ^ 8 * m + 5309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26498.1, data_15_26498.2]

/-- Complete interval computation for depth 15, residue 26499. -/
theorem bounds_15_26499 : exactInterval 15 26499 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26499 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26499) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26499 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26499 : oddCount 26499 15 = 8 ∧ acceleratedOrbit 15 26499 = 5309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26499 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26499) = 3 ^ 8 * m + 5309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26499.1, data_15_26499.2]

/-- Complete interval computation for depth 15, residue 26500. -/
theorem bounds_15_26500 : exactInterval 15 26500 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26500 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26500) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26500 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26500 : oddCount 26500 15 = 8 ∧ acceleratedOrbit 15 26500 = 5309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26500 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26500) = 3 ^ 8 * m + 5309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26500.1, data_15_26500.2]

/-- Complete interval computation for depth 15, residue 26501. -/
theorem bounds_15_26501 : exactInterval 15 26501 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26501 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26501) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26501 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26501 : oddCount 26501 15 = 8 ∧ acceleratedOrbit 15 26501 = 5309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26501 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26501) = 3 ^ 8 * m + 5309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26501.1, data_15_26501.2]

/-- Complete interval computation for depth 15, residue 26502. -/
theorem bounds_15_26502 : exactInterval 15 26502 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26502 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26502) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26502 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26502 : oddCount 26502 15 = 8 ∧ acceleratedOrbit 15 26502 = 5309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26502 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26502) = 3 ^ 8 * m + 5309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26502.1, data_15_26502.2]

/-- Complete interval computation for depth 15, residue 26503. -/
theorem bounds_15_26503 : exactInterval 15 26503 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26503 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26503) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26503 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26503 : oddCount 26503 15 = 8 ∧ acceleratedOrbit 15 26503 = 5309 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26503 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26503) = 3 ^ 8 * m + 5309 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26503.1, data_15_26503.2]

/-- Complete interval computation for depth 15, residue 26504. -/
theorem bounds_15_26504 : exactInterval 15 26504 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26504 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26504) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26504 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26504 : oddCount 26504 15 = 6 ∧ acceleratedOrbit 15 26504 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26504 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26504) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26504.1, data_15_26504.2]

/-- Complete interval computation for depth 15, residue 26505. -/
theorem bounds_15_26505 : exactInterval 15 26505 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26505 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26505) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26505 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26505 : oddCount 26505 15 = 9 ∧ acceleratedOrbit 15 26505 = 15923 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26505 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26505) = 3 ^ 9 * m + 15923 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26505.1, data_15_26505.2]

/-- Complete interval computation for depth 15, residue 26506. -/
theorem bounds_15_26506 : exactInterval 15 26506 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26506 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26506) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26506 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26506 : oddCount 26506 15 = 6 ∧ acceleratedOrbit 15 26506 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26506 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26506) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26506.1, data_15_26506.2]

/-- Complete interval computation for depth 15, residue 26507. -/
theorem bounds_15_26507 : exactInterval 15 26507 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26507 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26507) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26507 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26507 : oddCount 26507 15 = 8 ∧ acceleratedOrbit 15 26507 = 5308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26507 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26507) = 3 ^ 8 * m + 5308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26507.1, data_15_26507.2]

/-- Complete interval computation for depth 15, residue 26508. -/
theorem bounds_15_26508 : exactInterval 15 26508 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26508 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26508) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26508 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26508 : oddCount 26508 15 = 6 ∧ acceleratedOrbit 15 26508 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26508 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26508) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26508.1, data_15_26508.2]

end Collatz.Research.PassageAtlas.Batch0809
