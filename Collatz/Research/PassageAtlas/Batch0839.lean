import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0839

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27459. -/
theorem bounds_15_27459 : exactInterval 15 27459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27459 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27459) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27459 : oddCount 27459 15 = 6 ∧ acceleratedOrbit 15 27459 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27459 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27459) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27459.1, data_15_27459.2]

/-- Complete interval computation for depth 15, residue 27460. -/
theorem bounds_15_27460 : exactInterval 15 27460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27460 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27460) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27460 : oddCount 27460 15 = 7 ∧ acceleratedOrbit 15 27460 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27460 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27460) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27460.1, data_15_27460.2]

/-- Complete interval computation for depth 15, residue 27461. -/
theorem bounds_15_27461 : exactInterval 15 27461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27461 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27461) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27461 : oddCount 27461 15 = 7 ∧ acceleratedOrbit 15 27461 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27461 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27461) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27461.1, data_15_27461.2]

/-- Complete interval computation for depth 15, residue 27462. -/
theorem bounds_15_27462 : exactInterval 15 27462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27462 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27462) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27462 : oddCount 27462 15 = 7 ∧ acceleratedOrbit 15 27462 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27462 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27462) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27462.1, data_15_27462.2]

/-- Complete interval computation for depth 15, residue 27463. -/
theorem bounds_15_27463 : exactInterval 15 27463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27463 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27463) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27463 : oddCount 27463 15 = 10 ∧ acceleratedOrbit 15 27463 = 49493 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27463 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27463) = 3 ^ 10 * m + 49493 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27463.1, data_15_27463.2]

/-- Complete interval computation for depth 15, residue 27464. -/
theorem bounds_15_27464 : exactInterval 15 27464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27464 : oddCount 27464 15 = 7 ∧ acceleratedOrbit 15 27464 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27464) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27464.1, data_15_27464.2]

/-- Complete interval computation for depth 15, residue 27465. -/
theorem bounds_15_27465 : exactInterval 15 27465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27465 : oddCount 27465 15 = 8 ∧ acceleratedOrbit 15 27465 = 5501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27465) = 3 ^ 8 * m + 5501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27465.1, data_15_27465.2]

/-- Complete interval computation for depth 15, residue 27466. -/
theorem bounds_15_27466 : exactInterval 15 27466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27466 : oddCount 27466 15 = 7 ∧ acceleratedOrbit 15 27466 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27466) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27466.1, data_15_27466.2]

/-- Complete interval computation for depth 15, residue 27467. -/
theorem bounds_15_27467 : exactInterval 15 27467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27467 : oddCount 27467 15 = 7 ∧ acceleratedOrbit 15 27467 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27467) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27467.1, data_15_27467.2]

/-- Complete interval computation for depth 15, residue 27468. -/
theorem bounds_15_27468 : exactInterval 15 27468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27468 : oddCount 27468 15 = 7 ∧ acceleratedOrbit 15 27468 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27468) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27468.1, data_15_27468.2]

/-- Complete interval computation for depth 15, residue 27469. -/
theorem bounds_15_27469 : exactInterval 15 27469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27469 : oddCount 27469 15 = 7 ∧ acceleratedOrbit 15 27469 = 1835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27469) = 3 ^ 7 * m + 1835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27469.1, data_15_27469.2]

/-- Complete interval computation for depth 15, residue 27470. -/
theorem bounds_15_27470 : exactInterval 15 27470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27470 : oddCount 27470 15 = 8 ∧ acceleratedOrbit 15 27470 = 5501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27470) = 3 ^ 8 * m + 5501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27470.1, data_15_27470.2]

/-- Complete interval computation for depth 15, residue 27471. -/
theorem bounds_15_27471 : exactInterval 15 27471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27471 : oddCount 27471 15 = 8 ∧ acceleratedOrbit 15 27471 = 5501 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27471) = 3 ^ 8 * m + 5501 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27471.1, data_15_27471.2]

/-- Complete interval computation for depth 15, residue 27472. -/
theorem bounds_15_27472 : exactInterval 15 27472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27472 : oddCount 27472 15 = 5 ∧ acceleratedOrbit 15 27472 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27472) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27472.1, data_15_27472.2]

/-- Complete interval computation for depth 15, residue 27473. -/
theorem bounds_15_27473 : exactInterval 15 27473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27473 : oddCount 27473 15 = 10 ∧ acceleratedOrbit 15 27473 = 49517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27473) = 3 ^ 10 * m + 49517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27473.1, data_15_27473.2]

/-- Complete interval computation for depth 15, residue 27474. -/
theorem bounds_15_27474 : exactInterval 15 27474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27474 : oddCount 27474 15 = 10 ∧ acceleratedOrbit 15 27474 = 49517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27474) = 3 ^ 10 * m + 49517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27474.1, data_15_27474.2]

/-- Complete interval computation for depth 15, residue 27475. -/
theorem bounds_15_27475 : exactInterval 15 27475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27475 : oddCount 27475 15 = 10 ∧ acceleratedOrbit 15 27475 = 49517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27475) = 3 ^ 10 * m + 49517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27475.1, data_15_27475.2]

/-- Complete interval computation for depth 15, residue 27476. -/
theorem bounds_15_27476 : exactInterval 15 27476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27476 : oddCount 27476 15 = 5 ∧ acceleratedOrbit 15 27476 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27476) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27476.1, data_15_27476.2]

/-- Complete interval computation for depth 15, residue 27477. -/
theorem bounds_15_27477 : exactInterval 15 27477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27477 : oddCount 27477 15 = 5 ∧ acceleratedOrbit 15 27477 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27477) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27477.1, data_15_27477.2]

/-- Complete interval computation for depth 15, residue 27478. -/
theorem bounds_15_27478 : exactInterval 15 27478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27478 : oddCount 27478 15 = 8 ∧ acceleratedOrbit 15 27478 = 5503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27478) = 3 ^ 8 * m + 5503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27478.1, data_15_27478.2]

/-- Complete interval computation for depth 15, residue 27479. -/
theorem bounds_15_27479 : exactInterval 15 27479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27479 : oddCount 27479 15 = 8 ∧ acceleratedOrbit 15 27479 = 5503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27479) = 3 ^ 8 * m + 5503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27479.1, data_15_27479.2]

/-- Complete interval computation for depth 15, residue 27480. -/
theorem bounds_15_27480 : exactInterval 15 27480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27480 : oddCount 27480 15 = 8 ∧ acceleratedOrbit 15 27480 = 5507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27480) = 3 ^ 8 * m + 5507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27480.1, data_15_27480.2]

/-- Complete interval computation for depth 15, residue 27481. -/
theorem bounds_15_27481 : exactInterval 15 27481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27481 : oddCount 27481 15 = 8 ∧ acceleratedOrbit 15 27481 = 5507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27481) = 3 ^ 8 * m + 5507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27481.1, data_15_27481.2]

/-- Complete interval computation for depth 15, residue 27482. -/
theorem bounds_15_27482 : exactInterval 15 27482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27482 : oddCount 27482 15 = 8 ∧ acceleratedOrbit 15 27482 = 5507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27482) = 3 ^ 8 * m + 5507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27482.1, data_15_27482.2]

/-- Complete interval computation for depth 15, residue 27483. -/
theorem bounds_15_27483 : exactInterval 15 27483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27483 : oddCount 27483 15 = 9 ∧ acceleratedOrbit 15 27483 = 16510 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27483) = 3 ^ 9 * m + 16510 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27483.1, data_15_27483.2]

/-- Complete interval computation for depth 15, residue 27484. -/
theorem bounds_15_27484 : exactInterval 15 27484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27484 : oddCount 27484 15 = 8 ∧ acceleratedOrbit 15 27484 = 5507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27484) = 3 ^ 8 * m + 5507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27484.1, data_15_27484.2]

/-- Complete interval computation for depth 15, residue 27485. -/
theorem bounds_15_27485 : exactInterval 15 27485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27485 : oddCount 27485 15 = 8 ∧ acceleratedOrbit 15 27485 = 5507 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27485) = 3 ^ 8 * m + 5507 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27485.1, data_15_27485.2]

/-- Complete interval computation for depth 15, residue 27486. -/
theorem bounds_15_27486 : exactInterval 15 27486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27486 : oddCount 27486 15 = 9 ∧ acceleratedOrbit 15 27486 = 16514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27486) = 3 ^ 9 * m + 16514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27486.1, data_15_27486.2]

/-- Complete interval computation for depth 15, residue 27487. -/
theorem bounds_15_27487 : exactInterval 15 27487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27487 : oddCount 27487 15 = 9 ∧ acceleratedOrbit 15 27487 = 16514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27487) = 3 ^ 9 * m + 16514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27487.1, data_15_27487.2]

/-- Complete interval computation for depth 15, residue 27488. -/
theorem bounds_15_27488 : exactInterval 15 27488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27488 : oddCount 27488 15 = 7 ∧ acceleratedOrbit 15 27488 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27488) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27488.1, data_15_27488.2]

/-- Complete interval computation for depth 15, residue 27489. -/
theorem bounds_15_27489 : exactInterval 15 27489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27489 : oddCount 27489 15 = 11 ∧ acceleratedOrbit 15 27489 = 148625 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27489) = 3 ^ 11 * m + 148625 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27489.1, data_15_27489.2]

/-- Complete interval computation for depth 15, residue 27490. -/
theorem bounds_15_27490 : exactInterval 15 27490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27490 : oddCount 27490 15 = 4 ∧ acceleratedOrbit 15 27490 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27490) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27490.1, data_15_27490.2]

/-- Complete interval computation for depth 15, residue 27491. -/
theorem bounds_15_27491 : exactInterval 15 27491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27491 : oddCount 27491 15 = 4 ∧ acceleratedOrbit 15 27491 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27491) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27491.1, data_15_27491.2]

end Collatz.Research.PassageAtlas.Batch0839
