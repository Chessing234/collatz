import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0628

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2462. -/
theorem bounds_13_2462 : exactInterval 13 2462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2462 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2462) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2462 : oddCount 2462 13 = 7 ∧ acceleratedOrbit 13 2462 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2462 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2462) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2462.1, data_13_2462.2]

/-- Complete interval computation for depth 13, residue 2463. -/
theorem bounds_13_2463 : exactInterval 13 2463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2463 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2463) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2463 : oddCount 2463 13 = 9 ∧ acceleratedOrbit 13 2463 = 5921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2463 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2463) = 3 ^ 9 * m + 5921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2463.1, data_13_2463.2]

/-- Complete interval computation for depth 13, residue 2464. -/
theorem bounds_13_2464 : exactInterval 13 2464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2464 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2464) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2464 : oddCount 2464 13 = 4 ∧ acceleratedOrbit 13 2464 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2464 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2464) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2464.1, data_13_2464.2]

/-- Complete interval computation for depth 13, residue 2465. -/
theorem bounds_13_2465 : exactInterval 13 2465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2465 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2465) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2465 : oddCount 2465 13 = 7 ∧ acceleratedOrbit 13 2465 = 659 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2465 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2465) = 3 ^ 7 * m + 659 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2465.1, data_13_2465.2]

/-- Complete interval computation for depth 13, residue 2466. -/
theorem bounds_13_2466 : exactInterval 13 2466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2466 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2466) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2466 : oddCount 2466 13 = 7 ∧ acceleratedOrbit 13 2466 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2466 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2466) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2466.1, data_13_2466.2]

/-- Complete interval computation for depth 13, residue 2467. -/
theorem bounds_13_2467 : exactInterval 13 2467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2467 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2467) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2467 : oddCount 2467 13 = 7 ∧ acceleratedOrbit 13 2467 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2467 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2467) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2467.1, data_13_2467.2]

/-- Complete interval computation for depth 13, residue 2468. -/
theorem bounds_13_2468 : exactInterval 13 2468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2468 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2468) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2468 : oddCount 2468 13 = 7 ∧ acceleratedOrbit 13 2468 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2468 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2468) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2468.1, data_13_2468.2]

/-- Complete interval computation for depth 13, residue 2469. -/
theorem bounds_13_2469 : exactInterval 13 2469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2469 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2469) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2469 : oddCount 2469 13 = 7 ∧ acceleratedOrbit 13 2469 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2469 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2469) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2469.1, data_13_2469.2]

/-- Complete interval computation for depth 13, residue 2470. -/
theorem bounds_13_2470 : exactInterval 13 2470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2470 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2470) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2470 : oddCount 2470 13 = 7 ∧ acceleratedOrbit 13 2470 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2470 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2470) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2470.1, data_13_2470.2]

/-- Complete interval computation for depth 13, residue 2471. -/
theorem bounds_13_2471 : exactInterval 13 2471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2471 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2471) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2471 : oddCount 2471 13 = 6 ∧ acceleratedOrbit 13 2471 = 220 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2471 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2471) = 3 ^ 6 * m + 220 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2471.1, data_13_2471.2]

/-- Complete interval computation for depth 13, residue 2472. -/
theorem bounds_13_2472 : exactInterval 13 2472 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2472 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2472) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2472 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2472 : oddCount 2472 13 = 4 ∧ acceleratedOrbit 13 2472 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2472 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2472) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2472.1, data_13_2472.2]

/-- Complete interval computation for depth 13, residue 2473. -/
theorem bounds_13_2473 : exactInterval 13 2473 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2473 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2473) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2473 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2473 : oddCount 2473 13 = 8 ∧ acceleratedOrbit 13 2473 = 1982 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2473 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2473) = 3 ^ 8 * m + 1982 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2473.1, data_13_2473.2]

/-- Complete interval computation for depth 13, residue 2474. -/
theorem bounds_13_2474 : exactInterval 13 2474 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2474 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2474) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2474 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2474 : oddCount 2474 13 = 4 ∧ acceleratedOrbit 13 2474 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2474 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2474) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2474.1, data_13_2474.2]

/-- Complete interval computation for depth 13, residue 2475. -/
theorem bounds_13_2475 : exactInterval 13 2475 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2475 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2475) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2475 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2475 : oddCount 2475 13 = 9 ∧ acceleratedOrbit 13 2475 = 5953 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2475 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2475) = 3 ^ 9 * m + 5953 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2475.1, data_13_2475.2]

/-- Complete interval computation for depth 13, residue 2476. -/
theorem bounds_13_2476 : exactInterval 13 2476 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2476 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2476) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2476 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2476 : oddCount 2476 13 = 6 ∧ acceleratedOrbit 13 2476 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2476 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2476) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2476.1, data_13_2476.2]

/-- Complete interval computation for depth 13, residue 2477. -/
theorem bounds_13_2477 : exactInterval 13 2477 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2477 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2477) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2477 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2477 : oddCount 2477 13 = 6 ∧ acceleratedOrbit 13 2477 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2477 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2477) = 3 ^ 6 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2477.1, data_13_2477.2]

end Collatz.Research.StoppingAtlas.Batch0628
