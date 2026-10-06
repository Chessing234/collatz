import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0595

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19464. -/
theorem bounds_15_19464 : exactInterval 15 19464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19464 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19464) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19464 : oddCount 19464 15 = 6 ∧ acceleratedOrbit 15 19464 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19464 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19464) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19464.1, data_15_19464.2]

/-- Complete interval computation for depth 15, residue 19465. -/
theorem bounds_15_19465 : exactInterval 15 19465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19465 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19465) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19465 : oddCount 19465 15 = 8 ∧ acceleratedOrbit 15 19465 = 3898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19465 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19465) = 3 ^ 8 * m + 3898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19465.1, data_15_19465.2]

/-- Complete interval computation for depth 15, residue 19466. -/
theorem bounds_15_19466 : exactInterval 15 19466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19466 : oddCount 19466 15 = 6 ∧ acceleratedOrbit 15 19466 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19466) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19466.1, data_15_19466.2]

/-- Complete interval computation for depth 15, residue 19467. -/
theorem bounds_15_19467 : exactInterval 15 19467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19467 : oddCount 19467 15 = 6 ∧ acceleratedOrbit 15 19467 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19467) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19467.1, data_15_19467.2]

/-- Complete interval computation for depth 15, residue 19468. -/
theorem bounds_15_19468 : exactInterval 15 19468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19468 : oddCount 19468 15 = 6 ∧ acceleratedOrbit 15 19468 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19468) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19468.1, data_15_19468.2]

/-- Complete interval computation for depth 15, residue 19469. -/
theorem bounds_15_19469 : exactInterval 15 19469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19469 : oddCount 19469 15 = 6 ∧ acceleratedOrbit 15 19469 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19469) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19469.1, data_15_19469.2]

/-- Complete interval computation for depth 15, residue 19470. -/
theorem bounds_15_19470 : exactInterval 15 19470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19470 : oddCount 19470 15 = 7 ∧ acceleratedOrbit 15 19470 = 1300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19470) = 3 ^ 7 * m + 1300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19470.1, data_15_19470.2]

/-- Complete interval computation for depth 15, residue 19471. -/
theorem bounds_15_19471 : exactInterval 15 19471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19471 : oddCount 19471 15 = 7 ∧ acceleratedOrbit 15 19471 = 1300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19471) = 3 ^ 7 * m + 1300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19471.1, data_15_19471.2]

/-- Complete interval computation for depth 15, residue 19472. -/
theorem bounds_15_19472 : exactInterval 15 19472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19472 : oddCount 19472 15 = 5 ∧ acceleratedOrbit 15 19472 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19472) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19472.1, data_15_19472.2]

/-- Complete interval computation for depth 15, residue 19473. -/
theorem bounds_15_19473 : exactInterval 15 19473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19473 : oddCount 19473 15 = 6 ∧ acceleratedOrbit 15 19473 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19473) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19473.1, data_15_19473.2]

/-- Complete interval computation for depth 15, residue 19474. -/
theorem bounds_15_19474 : exactInterval 15 19474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19474 : oddCount 19474 15 = 8 ∧ acceleratedOrbit 15 19474 = 3901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19474) = 3 ^ 8 * m + 3901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19474.1, data_15_19474.2]

/-- Complete interval computation for depth 15, residue 19475. -/
theorem bounds_15_19475 : exactInterval 15 19475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19475 : oddCount 19475 15 = 8 ∧ acceleratedOrbit 15 19475 = 3901 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19475) = 3 ^ 8 * m + 3901 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19475.1, data_15_19475.2]

/-- Complete interval computation for depth 15, residue 19476. -/
theorem bounds_15_19476 : exactInterval 15 19476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19476 : oddCount 19476 15 = 5 ∧ acceleratedOrbit 15 19476 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19476) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19476.1, data_15_19476.2]

/-- Complete interval computation for depth 15, residue 19477. -/
theorem bounds_15_19477 : exactInterval 15 19477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19477 : oddCount 19477 15 = 5 ∧ acceleratedOrbit 15 19477 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19477) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19477.1, data_15_19477.2]

/-- Complete interval computation for depth 15, residue 19478. -/
theorem bounds_15_19478 : exactInterval 15 19478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19478 : oddCount 19478 15 = 6 ∧ acceleratedOrbit 15 19478 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19478) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19478.1, data_15_19478.2]

/-- Complete interval computation for depth 15, residue 19479. -/
theorem bounds_15_19479 : exactInterval 15 19479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19479 : oddCount 19479 15 = 6 ∧ acceleratedOrbit 15 19479 = 434 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19479) = 3 ^ 6 * m + 434 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19479.1, data_15_19479.2]

/-- Complete interval computation for depth 15, residue 19480. -/
theorem bounds_15_19480 : exactInterval 15 19480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19480 : oddCount 19480 15 = 5 ∧ acceleratedOrbit 15 19480 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19480) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19480.1, data_15_19480.2]

/-- Complete interval computation for depth 15, residue 19481. -/
theorem bounds_15_19481 : exactInterval 15 19481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19481 : oddCount 19481 15 = 10 ∧ acceleratedOrbit 15 19481 = 35113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19481) = 3 ^ 10 * m + 35113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19481.1, data_15_19481.2]

/-- Complete interval computation for depth 15, residue 19482. -/
theorem bounds_15_19482 : exactInterval 15 19482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19482 : oddCount 19482 15 = 5 ∧ acceleratedOrbit 15 19482 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19482) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19482.1, data_15_19482.2]

/-- Complete interval computation for depth 15, residue 19483. -/
theorem bounds_15_19483 : exactInterval 15 19483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19483 : oddCount 19483 15 = 12 ∧ acceleratedOrbit 15 19483 = 316007 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19483) = 3 ^ 12 * m + 316007 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19483.1, data_15_19483.2]

/-- Complete interval computation for depth 15, residue 19484. -/
theorem bounds_15_19484 : exactInterval 15 19484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19484 : oddCount 19484 15 = 7 ∧ acceleratedOrbit 15 19484 = 1301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19484) = 3 ^ 7 * m + 1301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19484.1, data_15_19484.2]

/-- Complete interval computation for depth 15, residue 19485. -/
theorem bounds_15_19485 : exactInterval 15 19485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19485 : oddCount 19485 15 = 7 ∧ acceleratedOrbit 15 19485 = 1301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19485) = 3 ^ 7 * m + 1301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19485.1, data_15_19485.2]

/-- Complete interval computation for depth 15, residue 19486. -/
theorem bounds_15_19486 : exactInterval 15 19486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19486 : oddCount 19486 15 = 7 ∧ acceleratedOrbit 15 19486 = 1301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19486) = 3 ^ 7 * m + 1301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19486.1, data_15_19486.2]

/-- Complete interval computation for depth 15, residue 19487. -/
theorem bounds_15_19487 : exactInterval 15 19487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19487 : oddCount 19487 15 = 11 ∧ acceleratedOrbit 15 19487 = 105356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19487) = 3 ^ 11 * m + 105356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19487.1, data_15_19487.2]

/-- Complete interval computation for depth 15, residue 19488. -/
theorem bounds_15_19488 : exactInterval 15 19488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19488 : oddCount 19488 15 = 5 ∧ acceleratedOrbit 15 19488 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19488) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19488.1, data_15_19488.2]

/-- Complete interval computation for depth 15, residue 19489. -/
theorem bounds_15_19489 : exactInterval 15 19489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19489 : oddCount 19489 15 = 7 ∧ acceleratedOrbit 15 19489 = 1301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19489) = 3 ^ 7 * m + 1301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19489.1, data_15_19489.2]

/-- Complete interval computation for depth 15, residue 19490. -/
theorem bounds_15_19490 : exactInterval 15 19490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19490 : oddCount 19490 15 = 5 ∧ acceleratedOrbit 15 19490 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19490) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19490.1, data_15_19490.2]

/-- Complete interval computation for depth 15, residue 19491. -/
theorem bounds_15_19491 : exactInterval 15 19491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19491 : oddCount 19491 15 = 5 ∧ acceleratedOrbit 15 19491 = 145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19491) = 3 ^ 5 * m + 145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19491.1, data_15_19491.2]

/-- Complete interval computation for depth 15, residue 19492. -/
theorem bounds_15_19492 : exactInterval 15 19492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19492 : oddCount 19492 15 = 8 ∧ acceleratedOrbit 15 19492 = 3905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19492) = 3 ^ 8 * m + 3905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19492.1, data_15_19492.2]

/-- Complete interval computation for depth 15, residue 19493. -/
theorem bounds_15_19493 : exactInterval 15 19493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19493 : oddCount 19493 15 = 8 ∧ acceleratedOrbit 15 19493 = 3905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19493) = 3 ^ 8 * m + 3905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19493.1, data_15_19493.2]

/-- Complete interval computation for depth 15, residue 19494. -/
theorem bounds_15_19494 : exactInterval 15 19494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19494 : oddCount 19494 15 = 8 ∧ acceleratedOrbit 15 19494 = 3905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19494) = 3 ^ 8 * m + 3905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19494.1, data_15_19494.2]

/-- Complete interval computation for depth 15, residue 19495. -/
theorem bounds_15_19495 : exactInterval 15 19495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19495 : oddCount 19495 15 = 8 ∧ acceleratedOrbit 15 19495 = 3905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19495) = 3 ^ 8 * m + 3905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19495.1, data_15_19495.2]

end Collatz.Research.PassageAtlas.Batch0595
