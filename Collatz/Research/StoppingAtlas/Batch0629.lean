import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0629

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2478. -/
theorem bounds_13_2478 : exactInterval 13 2478 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2478 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2478) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2478 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2478 : oddCount 2478 13 = 6 ∧ acceleratedOrbit 13 2478 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2478 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2478) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2478.1, data_13_2478.2]

/-- Complete interval computation for depth 13, residue 2479. -/
theorem bounds_13_2479 : exactInterval 13 2479 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2479 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2479) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2479 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2479 : oddCount 2479 13 = 8 ∧ acceleratedOrbit 13 2479 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2479 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2479) = 3 ^ 8 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2479.1, data_13_2479.2]

/-- Complete interval computation for depth 13, residue 2480. -/
theorem bounds_13_2480 : exactInterval 13 2480 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2480 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2480) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2480 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2480 : oddCount 2480 13 = 7 ∧ acceleratedOrbit 13 2480 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2480 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2480) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2480.1, data_13_2480.2]

/-- Complete interval computation for depth 13, residue 2481. -/
theorem bounds_13_2481 : exactInterval 13 2481 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2481 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2481) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2481 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2481 : oddCount 2481 13 = 5 ∧ acceleratedOrbit 13 2481 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2481 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2481) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2481.1, data_13_2481.2]

/-- Complete interval computation for depth 13, residue 2482. -/
theorem bounds_13_2482 : exactInterval 13 2482 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2482 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2482) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2482 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2482 : oddCount 2482 13 = 5 ∧ acceleratedOrbit 13 2482 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2482 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2482) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2482.1, data_13_2482.2]

/-- Complete interval computation for depth 13, residue 2483. -/
theorem bounds_13_2483 : exactInterval 13 2483 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2483 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2483) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2483 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2483 : oddCount 2483 13 = 5 ∧ acceleratedOrbit 13 2483 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2483 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2483) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2483.1, data_13_2483.2]

/-- Complete interval computation for depth 13, residue 2484. -/
theorem bounds_13_2484 : exactInterval 13 2484 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2484 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2484) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2484 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2484 : oddCount 2484 13 = 7 ∧ acceleratedOrbit 13 2484 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2484 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2484) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2484.1, data_13_2484.2]

/-- Complete interval computation for depth 13, residue 2485. -/
theorem bounds_13_2485 : exactInterval 13 2485 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2485 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2485) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2485 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2485 : oddCount 2485 13 = 7 ∧ acceleratedOrbit 13 2485 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2485 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2485) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2485.1, data_13_2485.2]

/-- Complete interval computation for depth 13, residue 2486. -/
theorem bounds_13_2486 : exactInterval 13 2486 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2486 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2486) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2486 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2486 : oddCount 2486 13 = 7 ∧ acceleratedOrbit 13 2486 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2486 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2486) = 3 ^ 7 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2486.1, data_13_2486.2]

/-- Complete interval computation for depth 13, residue 2487. -/
theorem bounds_13_2487 : exactInterval 13 2487 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2487 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2487) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2487 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2487 : oddCount 2487 13 = 7 ∧ acceleratedOrbit 13 2487 = 665 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2487 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2487) = 3 ^ 7 * m + 665 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2487.1, data_13_2487.2]

/-- Complete interval computation for depth 13, residue 2488. -/
theorem bounds_13_2488 : exactInterval 13 2488 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2488 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2488) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2488 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2488 : oddCount 2488 13 = 7 ∧ acceleratedOrbit 13 2488 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2488 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2488) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2488.1, data_13_2488.2]

/-- Complete interval computation for depth 13, residue 2489. -/
theorem bounds_13_2489 : exactInterval 13 2489 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2489 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2489) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2489 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2489 : oddCount 2489 13 = 5 ∧ acceleratedOrbit 13 2489 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2489 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2489) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2489.1, data_13_2489.2]

/-- Complete interval computation for depth 13, residue 2490. -/
theorem bounds_13_2490 : exactInterval 13 2490 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2490 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2490) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2490 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2490 : oddCount 2490 13 = 7 ∧ acceleratedOrbit 13 2490 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2490 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2490) = 3 ^ 7 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2490.1, data_13_2490.2]

/-- Complete interval computation for depth 13, residue 2491. -/
theorem bounds_13_2491 : exactInterval 13 2491 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2491 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2491) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2491 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2491 : oddCount 2491 13 = 9 ∧ acceleratedOrbit 13 2491 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2491 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2491) = 3 ^ 9 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2491.1, data_13_2491.2]

/-- Complete interval computation for depth 13, residue 2492. -/
theorem bounds_13_2492 : exactInterval 13 2492 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2492 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2492) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2492 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2492 : oddCount 2492 13 = 8 ∧ acceleratedOrbit 13 2492 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2492 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2492) = 3 ^ 8 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2492.1, data_13_2492.2]

end Collatz.Research.StoppingAtlas.Batch0629
