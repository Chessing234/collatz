import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0362

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2472. -/
theorem bounds_12_2472 : exactInterval 12 2472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2472 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2472) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2472 : oddCount 2472 12 = 3 ∧ acceleratedOrbit 12 2472 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2472 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2472) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2472.1, data_12_2472.2]

/-- Complete interval computation for depth 12, residue 2473. -/
theorem bounds_12_2473 : exactInterval 12 2473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2473 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2473) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2473 : oddCount 2473 12 = 8 ∧ acceleratedOrbit 12 2473 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2473 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2473) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2473.1, data_12_2473.2]

/-- Complete interval computation for depth 12, residue 2474. -/
theorem bounds_12_2474 : exactInterval 12 2474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2474 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2474) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2474 : oddCount 2474 12 = 3 ∧ acceleratedOrbit 12 2474 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2474 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2474) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2474.1, data_12_2474.2]

/-- Complete interval computation for depth 12, residue 2475. -/
theorem bounds_12_2475 : exactInterval 12 2475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2475 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2475) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2475 : oddCount 2475 12 = 9 ∧ acceleratedOrbit 12 2475 = 11906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2475 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2475) = 3 ^ 9 * m + 11906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2475.1, data_12_2475.2]

/-- Complete interval computation for depth 12, residue 2476. -/
theorem bounds_12_2476 : exactInterval 12 2476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2476 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2476) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2476 : oddCount 2476 12 = 6 ∧ acceleratedOrbit 12 2476 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2476 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2476) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2476.1, data_12_2476.2]

/-- Complete interval computation for depth 12, residue 2477. -/
theorem bounds_12_2477 : exactInterval 12 2477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2477 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2477) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2477 : oddCount 2477 12 = 6 ∧ acceleratedOrbit 12 2477 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2477 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2477) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2477.1, data_12_2477.2]

/-- Complete interval computation for depth 12, residue 2478. -/
theorem bounds_12_2478 : exactInterval 12 2478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2478 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2478) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2478 : oddCount 2478 12 = 6 ∧ acceleratedOrbit 12 2478 = 442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2478 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2478) = 3 ^ 6 * m + 442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2478.1, data_12_2478.2]

/-- Complete interval computation for depth 12, residue 2479. -/
theorem bounds_12_2479 : exactInterval 12 2479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2479 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2479) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2479 : oddCount 2479 12 = 7 ∧ acceleratedOrbit 12 2479 = 1325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2479 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2479) = 3 ^ 7 * m + 1325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2479.1, data_12_2479.2]

/-- Complete interval computation for depth 12, residue 2480. -/
theorem bounds_12_2480 : exactInterval 12 2480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2480 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2480) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2480 : oddCount 2480 12 = 6 ∧ acceleratedOrbit 12 2480 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2480 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2480) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2480.1, data_12_2480.2]

/-- Complete interval computation for depth 12, residue 2481. -/
theorem bounds_12_2481 : exactInterval 12 2481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2481 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2481) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2481 : oddCount 2481 12 = 5 ∧ acceleratedOrbit 12 2481 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2481 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2481) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2481.1, data_12_2481.2]

/-- Complete interval computation for depth 12, residue 2482. -/
theorem bounds_12_2482 : exactInterval 12 2482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2482 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2482) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2482 : oddCount 2482 12 = 5 ∧ acceleratedOrbit 12 2482 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2482 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2482) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2482.1, data_12_2482.2]

/-- Complete interval computation for depth 12, residue 2483. -/
theorem bounds_12_2483 : exactInterval 12 2483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2483 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2483) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2483 : oddCount 2483 12 = 5 ∧ acceleratedOrbit 12 2483 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2483 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2483) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2483.1, data_12_2483.2]

/-- Complete interval computation for depth 12, residue 2484. -/
theorem bounds_12_2484 : exactInterval 12 2484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2484 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2484) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2484 : oddCount 2484 12 = 6 ∧ acceleratedOrbit 12 2484 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2484 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2484) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2484.1, data_12_2484.2]

/-- Complete interval computation for depth 12, residue 2485. -/
theorem bounds_12_2485 : exactInterval 12 2485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2485 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2485) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2485 : oddCount 2485 12 = 6 ∧ acceleratedOrbit 12 2485 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2485 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2485) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2485.1, data_12_2485.2]

/-- Complete interval computation for depth 12, residue 2486. -/
theorem bounds_12_2486 : exactInterval 12 2486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2486 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2486) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2486 : oddCount 2486 12 = 6 ∧ acceleratedOrbit 12 2486 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2486 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2486) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2486.1, data_12_2486.2]

/-- Complete interval computation for depth 12, residue 2487. -/
theorem bounds_12_2487 : exactInterval 12 2487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2487 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2487) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2487 : oddCount 2487 12 = 6 ∧ acceleratedOrbit 12 2487 = 443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2487 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2487) = 3 ^ 6 * m + 443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2487.1, data_12_2487.2]

end Collatz.Research.StoppingAtlas.Batch0362
