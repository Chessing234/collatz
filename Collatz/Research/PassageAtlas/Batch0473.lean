import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0473

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15466. -/
theorem bounds_15_15466 : exactInterval 15 15466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15466 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15466) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15466 : oddCount 15466 15 = 3 ∧ acceleratedOrbit 15 15466 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15466 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15466) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15466.1, data_15_15466.2]

/-- Complete interval computation for depth 15, residue 15467. -/
theorem bounds_15_15467 : exactInterval 15 15467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15467 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15467) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15467 : oddCount 15467 15 = 10 ∧ acceleratedOrbit 15 15467 = 27877 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15467 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15467) = 3 ^ 10 * m + 27877 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15467.1, data_15_15467.2]

/-- Complete interval computation for depth 15, residue 15468. -/
theorem bounds_15_15468 : exactInterval 15 15468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15468 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15468) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15468 : oddCount 15468 15 = 10 ∧ acceleratedOrbit 15 15468 = 27884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15468 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15468) = 3 ^ 10 * m + 27884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15468.1, data_15_15468.2]

/-- Complete interval computation for depth 15, residue 15469. -/
theorem bounds_15_15469 : exactInterval 15 15469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15469 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15469) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15469 : oddCount 15469 15 = 10 ∧ acceleratedOrbit 15 15469 = 27884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15469 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15469) = 3 ^ 10 * m + 27884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15469.1, data_15_15469.2]

/-- Complete interval computation for depth 15, residue 15470. -/
theorem bounds_15_15470 : exactInterval 15 15470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15470 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15470) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15470 : oddCount 15470 15 = 10 ∧ acceleratedOrbit 15 15470 = 27884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15470 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15470) = 3 ^ 10 * m + 27884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15470.1, data_15_15470.2]

/-- Complete interval computation for depth 15, residue 15471. -/
theorem bounds_15_15471 : exactInterval 15 15471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15471 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15471) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15471 : oddCount 15471 15 = 12 ∧ acceleratedOrbit 15 15471 = 250937 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15471 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15471) = 3 ^ 12 * m + 250937 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15471.1, data_15_15471.2]

/-- Complete interval computation for depth 15, residue 15472. -/
theorem bounds_15_15472 : exactInterval 15 15472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15472 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15472) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15472 : oddCount 15472 15 = 8 ∧ acceleratedOrbit 15 15472 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15472 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15472) = 3 ^ 8 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15472.1, data_15_15472.2]

/-- Complete interval computation for depth 15, residue 15473. -/
theorem bounds_15_15473 : exactInterval 15 15473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15473 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15473) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15473 : oddCount 15473 15 = 3 ∧ acceleratedOrbit 15 15473 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15473 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15473) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15473.1, data_15_15473.2]

/-- Complete interval computation for depth 15, residue 15474. -/
theorem bounds_15_15474 : exactInterval 15 15474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15474 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15474) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15474 : oddCount 15474 15 = 8 ∧ acceleratedOrbit 15 15474 = 3100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15474 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15474) = 3 ^ 8 * m + 3100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15474.1, data_15_15474.2]

/-- Complete interval computation for depth 15, residue 15475. -/
theorem bounds_15_15475 : exactInterval 15 15475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15475 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15475) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15475 : oddCount 15475 15 = 8 ∧ acceleratedOrbit 15 15475 = 3100 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15475 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15475) = 3 ^ 8 * m + 3100 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15475.1, data_15_15475.2]

/-- Complete interval computation for depth 15, residue 15476. -/
theorem bounds_15_15476 : exactInterval 15 15476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15476 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15476) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15476 : oddCount 15476 15 = 8 ∧ acceleratedOrbit 15 15476 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15476 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15476) = 3 ^ 8 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15476.1, data_15_15476.2]

/-- Complete interval computation for depth 15, residue 15477. -/
theorem bounds_15_15477 : exactInterval 15 15477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15477 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15477) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15477 : oddCount 15477 15 = 8 ∧ acceleratedOrbit 15 15477 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15477 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15477) = 3 ^ 8 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15477.1, data_15_15477.2]

/-- Complete interval computation for depth 15, residue 15478. -/
theorem bounds_15_15478 : exactInterval 15 15478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15478 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15478) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15478 : oddCount 15478 15 = 7 ∧ acceleratedOrbit 15 15478 = 1034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15478 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15478) = 3 ^ 7 * m + 1034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15478.1, data_15_15478.2]

/-- Complete interval computation for depth 15, residue 15479. -/
theorem bounds_15_15479 : exactInterval 15 15479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15479 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15479) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15479 : oddCount 15479 15 = 7 ∧ acceleratedOrbit 15 15479 = 1034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15479 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15479) = 3 ^ 7 * m + 1034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15479.1, data_15_15479.2]

/-- Complete interval computation for depth 15, residue 15480. -/
theorem bounds_15_15480 : exactInterval 15 15480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15480 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15480) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15480 : oddCount 15480 15 = 8 ∧ acceleratedOrbit 15 15480 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15480 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15480) = 3 ^ 8 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15480.1, data_15_15480.2]

/-- Complete interval computation for depth 15, residue 15481. -/
theorem bounds_15_15481 : exactInterval 15 15481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15481 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15481) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15481 : oddCount 15481 15 = 9 ∧ acceleratedOrbit 15 15481 = 9301 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15481 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15481) = 3 ^ 9 * m + 9301 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15481.1, data_15_15481.2]

/-- Complete interval computation for depth 15, residue 15482. -/
theorem bounds_15_15482 : exactInterval 15 15482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15482 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15482) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15482 : oddCount 15482 15 = 8 ∧ acceleratedOrbit 15 15482 = 3104 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15482 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15482) = 3 ^ 8 * m + 3104 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15482.1, data_15_15482.2]

/-- Complete interval computation for depth 15, residue 15483. -/
theorem bounds_15_15483 : exactInterval 15 15483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15483 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15483) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15483 : oddCount 15483 15 = 7 ∧ acceleratedOrbit 15 15483 = 1034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15483 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15483) = 3 ^ 7 * m + 1034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15483.1, data_15_15483.2]

/-- Complete interval computation for depth 15, residue 15484. -/
theorem bounds_15_15484 : exactInterval 15 15484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15484 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15484) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15484 : oddCount 15484 15 = 9 ∧ acceleratedOrbit 15 15484 = 9305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15484 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15484) = 3 ^ 9 * m + 9305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15484.1, data_15_15484.2]

/-- Complete interval computation for depth 15, residue 15485. -/
theorem bounds_15_15485 : exactInterval 15 15485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15485 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15485) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15485 : oddCount 15485 15 = 9 ∧ acceleratedOrbit 15 15485 = 9305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15485 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15485) = 3 ^ 9 * m + 9305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15485.1, data_15_15485.2]

/-- Complete interval computation for depth 15, residue 15486. -/
theorem bounds_15_15486 : exactInterval 15 15486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15486 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15486) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15486 : oddCount 15486 15 = 9 ∧ acceleratedOrbit 15 15486 = 9305 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15486 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15486) = 3 ^ 9 * m + 9305 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15486.1, data_15_15486.2]

/-- Complete interval computation for depth 15, residue 15487. -/
theorem bounds_15_15487 : exactInterval 15 15487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15487 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15487) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15487 : oddCount 15487 15 = 10 ∧ acceleratedOrbit 15 15487 = 27910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15487 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15487) = 3 ^ 10 * m + 27910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15487.1, data_15_15487.2]

/-- Complete interval computation for depth 15, residue 15488. -/
theorem bounds_15_15488 : exactInterval 15 15488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15488 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15488) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15488 : oddCount 15488 15 = 6 ∧ acceleratedOrbit 15 15488 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15488 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15488) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15488.1, data_15_15488.2]

/-- Complete interval computation for depth 15, residue 15489. -/
theorem bounds_15_15489 : exactInterval 15 15489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15489 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15489) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15489 : oddCount 15489 15 = 7 ∧ acceleratedOrbit 15 15489 = 1034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15489 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15489) = 3 ^ 7 * m + 1034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15489.1, data_15_15489.2]

/-- Complete interval computation for depth 15, residue 15490. -/
theorem bounds_15_15490 : exactInterval 15 15490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15490 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15490) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15490 : oddCount 15490 15 = 5 ∧ acceleratedOrbit 15 15490 = 115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15490 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15490) = 3 ^ 5 * m + 115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15490.1, data_15_15490.2]

/-- Complete interval computation for depth 15, residue 15491. -/
theorem bounds_15_15491 : exactInterval 15 15491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15491 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15491) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15491 : oddCount 15491 15 = 5 ∧ acceleratedOrbit 15 15491 = 115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15491 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15491) = 3 ^ 5 * m + 115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15491.1, data_15_15491.2]

/-- Complete interval computation for depth 15, residue 15492. -/
theorem bounds_15_15492 : exactInterval 15 15492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15492 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15492) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15492 : oddCount 15492 15 = 5 ∧ acceleratedOrbit 15 15492 = 115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15492 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15492) = 3 ^ 5 * m + 115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15492.1, data_15_15492.2]

/-- Complete interval computation for depth 15, residue 15493. -/
theorem bounds_15_15493 : exactInterval 15 15493 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15493 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15493) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15493 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15493 : oddCount 15493 15 = 5 ∧ acceleratedOrbit 15 15493 = 115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15493 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15493) = 3 ^ 5 * m + 115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15493.1, data_15_15493.2]

/-- Complete interval computation for depth 15, residue 15494. -/
theorem bounds_15_15494 : exactInterval 15 15494 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15494 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15494) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15494 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15494 : oddCount 15494 15 = 5 ∧ acceleratedOrbit 15 15494 = 115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15494 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15494) = 3 ^ 5 * m + 115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15494.1, data_15_15494.2]

/-- Complete interval computation for depth 15, residue 15495. -/
theorem bounds_15_15495 : exactInterval 15 15495 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15495 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15495) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15495 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15495 : oddCount 15495 15 = 9 ∧ acceleratedOrbit 15 15495 = 9310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15495 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15495) = 3 ^ 9 * m + 9310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15495.1, data_15_15495.2]

/-- Complete interval computation for depth 15, residue 15496. -/
theorem bounds_15_15496 : exactInterval 15 15496 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15496 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15496) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15496 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15496 : oddCount 15496 15 = 6 ∧ acceleratedOrbit 15 15496 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15496 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15496) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15496.1, data_15_15496.2]

/-- Complete interval computation for depth 15, residue 15497. -/
theorem bounds_15_15497 : exactInterval 15 15497 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15497 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15497) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15497 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15497 : oddCount 15497 15 = 12 ∧ acceleratedOrbit 15 15497 = 251369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15497 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15497) = 3 ^ 12 * m + 251369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15497.1, data_15_15497.2]

/-- Complete interval computation for depth 15, residue 15498. -/
theorem bounds_15_15498 : exactInterval 15 15498 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15498 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15498) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15498 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15498 : oddCount 15498 15 = 6 ∧ acceleratedOrbit 15 15498 = 346 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15498 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15498) = 3 ^ 6 * m + 346 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15498.1, data_15_15498.2]

end Collatz.Research.PassageAtlas.Batch0473
