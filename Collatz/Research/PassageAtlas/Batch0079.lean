import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0079

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2555. -/
theorem bounds_15_2555 : exactInterval 15 2555 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2555 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2555) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2555 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2555 : oddCount 2555 15 = 9 ∧ acceleratedOrbit 15 2555 = 1538 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2555 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2555) = 3 ^ 9 * m + 1538 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2555.1, data_15_2555.2]

/-- Complete interval computation for depth 15, residue 2556. -/
theorem bounds_15_2556 : exactInterval 15 2556 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2556 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2556) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2556 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2556 : oddCount 2556 15 = 11 ∧ acceleratedOrbit 15 2556 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2556 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2556) = 3 ^ 11 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2556.1, data_15_2556.2]

/-- Complete interval computation for depth 15, residue 2557. -/
theorem bounds_15_2557 : exactInterval 15 2557 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2557 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2557) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2557 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2557 : oddCount 2557 15 = 11 ∧ acceleratedOrbit 15 2557 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2557 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2557) = 3 ^ 11 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2557.1, data_15_2557.2]

/-- Complete interval computation for depth 15, residue 2558. -/
theorem bounds_15_2558 : exactInterval 15 2558 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2558 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2558) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2558 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2558 : oddCount 2558 15 = 11 ∧ acceleratedOrbit 15 2558 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2558 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2558) = 3 ^ 11 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2558.1, data_15_2558.2]

/-- Complete interval computation for depth 15, residue 2559. -/
theorem bounds_15_2559 : exactInterval 15 2559 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2559 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2559) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2559 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2559 : oddCount 2559 15 = 12 ∧ acceleratedOrbit 15 2559 = 41519 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2559 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2559) = 3 ^ 12 * m + 41519 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2559.1, data_15_2559.2]

/-- Complete interval computation for depth 15, residue 2560. -/
theorem bounds_15_2560 : exactInterval 15 2560 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2560 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2560) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2560 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2560 : oddCount 2560 15 = 2 ∧ acceleratedOrbit 15 2560 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2560 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2560) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2560.1, data_15_2560.2]

/-- Complete interval computation for depth 15, residue 2561. -/
theorem bounds_15_2561 : exactInterval 15 2561 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2561 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2561) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2561 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2561 : oddCount 2561 15 = 8 ∧ acceleratedOrbit 15 2561 = 514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2561 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2561) = 3 ^ 8 * m + 514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2561.1, data_15_2561.2]

/-- Complete interval computation for depth 15, residue 2562. -/
theorem bounds_15_2562 : exactInterval 15 2562 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2562 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2562) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2562 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2562 : oddCount 2562 15 = 7 ∧ acceleratedOrbit 15 2562 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2562 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2562) = 3 ^ 7 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2562.1, data_15_2562.2]

/-- Complete interval computation for depth 15, residue 2563. -/
theorem bounds_15_2563 : exactInterval 15 2563 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2563 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2563) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2563 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2563 : oddCount 2563 15 = 7 ∧ acceleratedOrbit 15 2563 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2563 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2563) = 3 ^ 7 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2563.1, data_15_2563.2]

/-- Complete interval computation for depth 15, residue 2564. -/
theorem bounds_15_2564 : exactInterval 15 2564 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2564 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2564) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2564 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2564 : oddCount 2564 15 = 7 ∧ acceleratedOrbit 15 2564 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2564 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2564) = 3 ^ 7 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2564.1, data_15_2564.2]

/-- Complete interval computation for depth 15, residue 2565. -/
theorem bounds_15_2565 : exactInterval 15 2565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2565 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2565) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2565 : oddCount 2565 15 = 7 ∧ acceleratedOrbit 15 2565 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2565 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2565) = 3 ^ 7 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2565.1, data_15_2565.2]

/-- Complete interval computation for depth 15, residue 2566. -/
theorem bounds_15_2566 : exactInterval 15 2566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2566 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2566) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2566 : oddCount 2566 15 = 7 ∧ acceleratedOrbit 15 2566 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2566 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2566) = 3 ^ 7 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2566.1, data_15_2566.2]

/-- Complete interval computation for depth 15, residue 2567. -/
theorem bounds_15_2567 : exactInterval 15 2567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2567 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2567) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2567 : oddCount 2567 15 = 8 ∧ acceleratedOrbit 15 2567 = 515 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2567 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2567) = 3 ^ 8 * m + 515 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2567.1, data_15_2567.2]

/-- Complete interval computation for depth 15, residue 2568. -/
theorem bounds_15_2568 : exactInterval 15 2568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2568 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2568) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2568 : oddCount 2568 15 = 5 ∧ acceleratedOrbit 15 2568 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2568 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2568) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2568.1, data_15_2568.2]

/-- Complete interval computation for depth 15, residue 2569. -/
theorem bounds_15_2569 : exactInterval 15 2569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2569 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2569) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2569 : oddCount 2569 15 = 7 ∧ acceleratedOrbit 15 2569 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2569 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2569) = 3 ^ 7 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2569.1, data_15_2569.2]

/-- Complete interval computation for depth 15, residue 2570. -/
theorem bounds_15_2570 : exactInterval 15 2570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2570 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2570) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2570 : oddCount 2570 15 = 5 ∧ acceleratedOrbit 15 2570 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2570 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2570) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2570.1, data_15_2570.2]

/-- Complete interval computation for depth 15, residue 2571. -/
theorem bounds_15_2571 : exactInterval 15 2571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2571 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2571) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2571 : oddCount 2571 15 = 7 ∧ acceleratedOrbit 15 2571 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2571 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2571) = 3 ^ 7 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2571.1, data_15_2571.2]

/-- Complete interval computation for depth 15, residue 2572. -/
theorem bounds_15_2572 : exactInterval 15 2572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2572 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2572) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2572 : oddCount 2572 15 = 5 ∧ acceleratedOrbit 15 2572 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2572 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2572) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2572.1, data_15_2572.2]

/-- Complete interval computation for depth 15, residue 2573. -/
theorem bounds_15_2573 : exactInterval 15 2573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2573 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2573) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2573 : oddCount 2573 15 = 5 ∧ acceleratedOrbit 15 2573 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2573 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2573) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2573.1, data_15_2573.2]

/-- Complete interval computation for depth 15, residue 2574. -/
theorem bounds_15_2574 : exactInterval 15 2574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2574 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2574) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2574 : oddCount 2574 15 = 9 ∧ acceleratedOrbit 15 2574 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2574 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2574) = 3 ^ 9 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2574.1, data_15_2574.2]

/-- Complete interval computation for depth 15, residue 2575. -/
theorem bounds_15_2575 : exactInterval 15 2575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2575 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2575) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2575 : oddCount 2575 15 = 9 ∧ acceleratedOrbit 15 2575 = 1549 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2575 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2575) = 3 ^ 9 * m + 1549 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2575.1, data_15_2575.2]

/-- Complete interval computation for depth 15, residue 2576. -/
theorem bounds_15_2576 : exactInterval 15 2576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2576 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2576) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2576 : oddCount 2576 15 = 7 ∧ acceleratedOrbit 15 2576 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2576 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2576) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2576.1, data_15_2576.2]

/-- Complete interval computation for depth 15, residue 2577. -/
theorem bounds_15_2577 : exactInterval 15 2577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2577 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2577) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2577 : oddCount 2577 15 = 5 ∧ acceleratedOrbit 15 2577 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2577 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2577) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2577.1, data_15_2577.2]

/-- Complete interval computation for depth 15, residue 2578. -/
theorem bounds_15_2578 : exactInterval 15 2578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2578 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2578) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2578 : oddCount 2578 15 = 9 ∧ acceleratedOrbit 15 2578 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2578 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2578) = 3 ^ 9 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2578.1, data_15_2578.2]

/-- Complete interval computation for depth 15, residue 2579. -/
theorem bounds_15_2579 : exactInterval 15 2579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2579 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2579) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2579 : oddCount 2579 15 = 9 ∧ acceleratedOrbit 15 2579 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2579 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2579) = 3 ^ 9 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2579.1, data_15_2579.2]

/-- Complete interval computation for depth 15, residue 2580. -/
theorem bounds_15_2580 : exactInterval 15 2580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2580 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2580) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2580 : oddCount 2580 15 = 7 ∧ acceleratedOrbit 15 2580 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2580 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2580) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2580.1, data_15_2580.2]

/-- Complete interval computation for depth 15, residue 2581. -/
theorem bounds_15_2581 : exactInterval 15 2581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2581 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2581) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2581 : oddCount 2581 15 = 7 ∧ acceleratedOrbit 15 2581 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2581 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2581) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2581.1, data_15_2581.2]

/-- Complete interval computation for depth 15, residue 2582. -/
theorem bounds_15_2582 : exactInterval 15 2582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2582 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2582) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2582 : oddCount 2582 15 = 7 ∧ acceleratedOrbit 15 2582 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2582 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2582) = 3 ^ 7 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2582.1, data_15_2582.2]

/-- Complete interval computation for depth 15, residue 2583. -/
theorem bounds_15_2583 : exactInterval 15 2583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2583 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2583) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2583 : oddCount 2583 15 = 7 ∧ acceleratedOrbit 15 2583 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2583 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2583) = 3 ^ 7 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2583.1, data_15_2583.2]

/-- Complete interval computation for depth 15, residue 2584. -/
theorem bounds_15_2584 : exactInterval 15 2584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2584 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2584) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2584 : oddCount 2584 15 = 7 ∧ acceleratedOrbit 15 2584 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2584 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2584) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2584.1, data_15_2584.2]

/-- Complete interval computation for depth 15, residue 2585. -/
theorem bounds_15_2585 : exactInterval 15 2585 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2585 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2585) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2585 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2585 : oddCount 2585 15 = 7 ∧ acceleratedOrbit 15 2585 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2585 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2585) = 3 ^ 7 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2585.1, data_15_2585.2]

/-- Complete interval computation for depth 15, residue 2586. -/
theorem bounds_15_2586 : exactInterval 15 2586 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2586 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2586) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2586 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2586 : oddCount 2586 15 = 7 ∧ acceleratedOrbit 15 2586 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2586 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2586) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2586.1, data_15_2586.2]

/-- Complete interval computation for depth 15, residue 2587. -/
theorem bounds_15_2587 : exactInterval 15 2587 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2587 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2587) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2587 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2587 : oddCount 2587 15 = 9 ∧ acceleratedOrbit 15 2587 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2587 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2587) = 3 ^ 9 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2587.1, data_15_2587.2]

end Collatz.Research.PassageAtlas.Batch0079
