import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0635

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2570. -/
theorem bounds_13_2570 : exactInterval 13 2570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2570 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2570) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2570 : oddCount 2570 13 = 4 ∧ acceleratedOrbit 13 2570 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2570 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2570) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2570.1, data_13_2570.2]

/-- Complete interval computation for depth 13, residue 2571. -/
theorem bounds_13_2571 : exactInterval 13 2571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2571 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2571) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2571 : oddCount 2571 13 = 7 ∧ acceleratedOrbit 13 2571 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2571 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2571) = 3 ^ 7 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2571.1, data_13_2571.2]

/-- Complete interval computation for depth 13, residue 2572. -/
theorem bounds_13_2572 : exactInterval 13 2572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2572 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2572) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2572 : oddCount 2572 13 = 4 ∧ acceleratedOrbit 13 2572 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2572 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2572) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2572.1, data_13_2572.2]

/-- Complete interval computation for depth 13, residue 2573. -/
theorem bounds_13_2573 : exactInterval 13 2573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2573 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2573) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2573 : oddCount 2573 13 = 4 ∧ acceleratedOrbit 13 2573 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2573 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2573) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2573.1, data_13_2573.2]

/-- Complete interval computation for depth 13, residue 2574. -/
theorem bounds_13_2574 : exactInterval 13 2574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2574 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2574) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2574 : oddCount 2574 13 = 8 ∧ acceleratedOrbit 13 2574 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2574 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2574) = 3 ^ 8 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2574.1, data_13_2574.2]

/-- Complete interval computation for depth 13, residue 2575. -/
theorem bounds_13_2575 : exactInterval 13 2575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2575 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2575) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2575 : oddCount 2575 13 = 8 ∧ acceleratedOrbit 13 2575 = 2065 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2575 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2575) = 3 ^ 8 * m + 2065 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2575.1, data_13_2575.2]

/-- Complete interval computation for depth 13, residue 2576. -/
theorem bounds_13_2576 : exactInterval 13 2576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2576 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2576) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2576 : oddCount 2576 13 = 6 ∧ acceleratedOrbit 13 2576 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2576 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2576) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2576.1, data_13_2576.2]

/-- Complete interval computation for depth 13, residue 2577. -/
theorem bounds_13_2577 : exactInterval 13 2577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2577 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2577) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2577 : oddCount 2577 13 = 4 ∧ acceleratedOrbit 13 2577 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2577 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2577) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2577.1, data_13_2577.2]

/-- Complete interval computation for depth 13, residue 2578. -/
theorem bounds_13_2578 : exactInterval 13 2578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2578 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2578) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2578 : oddCount 2578 13 = 8 ∧ acceleratedOrbit 13 2578 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2578 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2578) = 3 ^ 8 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2578.1, data_13_2578.2]

/-- Complete interval computation for depth 13, residue 2579. -/
theorem bounds_13_2579 : exactInterval 13 2579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2579 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2579) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2579 : oddCount 2579 13 = 8 ∧ acceleratedOrbit 13 2579 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2579 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2579) = 3 ^ 8 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2579.1, data_13_2579.2]

/-- Complete interval computation for depth 13, residue 2580. -/
theorem bounds_13_2580 : exactInterval 13 2580 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2580 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2580) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2580 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2580 : oddCount 2580 13 = 6 ∧ acceleratedOrbit 13 2580 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2580 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2580) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2580.1, data_13_2580.2]

/-- Complete interval computation for depth 13, residue 2581. -/
theorem bounds_13_2581 : exactInterval 13 2581 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2581 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2581) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2581 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2581 : oddCount 2581 13 = 6 ∧ acceleratedOrbit 13 2581 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2581 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2581) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2581.1, data_13_2581.2]

/-- Complete interval computation for depth 13, residue 2582. -/
theorem bounds_13_2582 : exactInterval 13 2582 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2582 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2582) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2582 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2582 : oddCount 2582 13 = 7 ∧ acceleratedOrbit 13 2582 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2582 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2582) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2582.1, data_13_2582.2]

/-- Complete interval computation for depth 13, residue 2583. -/
theorem bounds_13_2583 : exactInterval 13 2583 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2583 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2583) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2583 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2583 : oddCount 2583 13 = 7 ∧ acceleratedOrbit 13 2583 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2583 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2583) = 3 ^ 7 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2583.1, data_13_2583.2]

/-- Complete interval computation for depth 13, residue 2584. -/
theorem bounds_13_2584 : exactInterval 13 2584 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2584 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2584) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2584 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2584 : oddCount 2584 13 = 6 ∧ acceleratedOrbit 13 2584 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2584 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2584) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2584.1, data_13_2584.2]

end Collatz.Research.StoppingAtlas.Batch0635
