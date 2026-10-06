import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0361

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2457. -/
theorem bounds_12_2457 : exactInterval 12 2457 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2457 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2457) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2457 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2457 : oddCount 2457 12 = 5 ∧ acceleratedOrbit 12 2457 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2457 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2457) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2457.1, data_12_2457.2]

/-- Complete interval computation for depth 12, residue 2458. -/
theorem bounds_12_2458 : exactInterval 12 2458 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2458 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2458) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2458 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2458 : oddCount 2458 12 = 4 ∧ acceleratedOrbit 12 2458 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2458 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2458) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2458.1, data_12_2458.2]

/-- Complete interval computation for depth 12, residue 2459. -/
theorem bounds_12_2459 : exactInterval 12 2459 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2459 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2459) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2459 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2459 : oddCount 2459 12 = 9 ∧ acceleratedOrbit 12 2459 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2459 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2459) = 3 ^ 9 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2459.1, data_12_2459.2]

/-- Complete interval computation for depth 12, residue 2460. -/
theorem bounds_12_2460 : exactInterval 12 2460 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2460 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2460) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2460 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2460 : oddCount 2460 12 = 7 ∧ acceleratedOrbit 12 2460 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2460 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2460) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2460.1, data_12_2460.2]

/-- Complete interval computation for depth 12, residue 2461. -/
theorem bounds_12_2461 : exactInterval 12 2461 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2461 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2461) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2461 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2461 : oddCount 2461 12 = 7 ∧ acceleratedOrbit 12 2461 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2461 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2461) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2461.1, data_12_2461.2]

/-- Complete interval computation for depth 12, residue 2462. -/
theorem bounds_12_2462 : exactInterval 12 2462 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2462 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2462) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2462 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2462 : oddCount 2462 12 = 7 ∧ acceleratedOrbit 12 2462 = 1316 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2462 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2462) = 3 ^ 7 * m + 1316 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2462.1, data_12_2462.2]

/-- Complete interval computation for depth 12, residue 2463. -/
theorem bounds_12_2463 : exactInterval 12 2463 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2463 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2463) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2463 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2463 : oddCount 2463 12 = 8 ∧ acceleratedOrbit 12 2463 = 3947 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2463 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2463) = 3 ^ 8 * m + 3947 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2463.1, data_12_2463.2]

/-- Complete interval computation for depth 12, residue 2464. -/
theorem bounds_12_2464 : exactInterval 12 2464 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2464 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2464) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2464 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2464 : oddCount 2464 12 = 3 ∧ acceleratedOrbit 12 2464 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2464 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2464) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2464.1, data_12_2464.2]

/-- Complete interval computation for depth 12, residue 2465. -/
theorem bounds_12_2465 : exactInterval 12 2465 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2465 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2465) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2465 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2465 : oddCount 2465 12 = 7 ∧ acceleratedOrbit 12 2465 = 1318 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2465 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2465) = 3 ^ 7 * m + 1318 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2465.1, data_12_2465.2]

/-- Complete interval computation for depth 12, residue 2466. -/
theorem bounds_12_2466 : exactInterval 12 2466 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2466 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2466) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2466 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2466 : oddCount 2466 12 = 7 ∧ acceleratedOrbit 12 2466 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2466 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2466) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2466.1, data_12_2466.2]

/-- Complete interval computation for depth 12, residue 2467. -/
theorem bounds_12_2467 : exactInterval 12 2467 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2467 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2467) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2467 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2467 : oddCount 2467 12 = 7 ∧ acceleratedOrbit 12 2467 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2467 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2467) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2467.1, data_12_2467.2]

/-- Complete interval computation for depth 12, residue 2468. -/
theorem bounds_12_2468 : exactInterval 12 2468 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2468 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2468) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2468 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2468 : oddCount 2468 12 = 7 ∧ acceleratedOrbit 12 2468 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2468 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2468) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2468.1, data_12_2468.2]

/-- Complete interval computation for depth 12, residue 2469. -/
theorem bounds_12_2469 : exactInterval 12 2469 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2469 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2469) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2469 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2469 : oddCount 2469 12 = 7 ∧ acceleratedOrbit 12 2469 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2469 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2469) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2469.1, data_12_2469.2]

/-- Complete interval computation for depth 12, residue 2470. -/
theorem bounds_12_2470 : exactInterval 12 2470 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2470 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2470) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2470 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2470 : oddCount 2470 12 = 7 ∧ acceleratedOrbit 12 2470 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2470 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2470) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2470.1, data_12_2470.2]

/-- Complete interval computation for depth 12, residue 2471. -/
theorem bounds_12_2471 : exactInterval 12 2471 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2471 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2471) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2471 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2471 : oddCount 2471 12 = 6 ∧ acceleratedOrbit 12 2471 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2471 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2471) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2471.1, data_12_2471.2]

end Collatz.Research.StoppingAtlas.Batch0361
