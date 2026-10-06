import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0368

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2565. -/
theorem bounds_12_2565 : exactInterval 12 2565 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2565 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2565) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2565 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2565 : oddCount 2565 12 = 7 ∧ acceleratedOrbit 12 2565 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2565 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2565) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2565.1, data_12_2565.2]

/-- Complete interval computation for depth 12, residue 2566. -/
theorem bounds_12_2566 : exactInterval 12 2566 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2566 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2566) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2566 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2566 : oddCount 2566 12 = 7 ∧ acceleratedOrbit 12 2566 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2566 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2566) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2566.1, data_12_2566.2]

/-- Complete interval computation for depth 12, residue 2567. -/
theorem bounds_12_2567 : exactInterval 12 2567 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2567 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2567) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2567 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2567 : oddCount 2567 12 = 7 ∧ acceleratedOrbit 12 2567 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2567 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2567) = 3 ^ 7 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2567.1, data_12_2567.2]

/-- Complete interval computation for depth 12, residue 2568. -/
theorem bounds_12_2568 : exactInterval 12 2568 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2568 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2568) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2568 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2568 : oddCount 2568 12 = 3 ∧ acceleratedOrbit 12 2568 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2568 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2568) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2568.1, data_12_2568.2]

/-- Complete interval computation for depth 12, residue 2569. -/
theorem bounds_12_2569 : exactInterval 12 2569 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2569 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2569) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2569 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2569 : oddCount 2569 12 = 6 ∧ acceleratedOrbit 12 2569 = 458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2569 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2569) = 3 ^ 6 * m + 458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2569.1, data_12_2569.2]

/-- Complete interval computation for depth 12, residue 2570. -/
theorem bounds_12_2570 : exactInterval 12 2570 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2570 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2570) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2570 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2570 : oddCount 2570 12 = 3 ∧ acceleratedOrbit 12 2570 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2570 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2570) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2570.1, data_12_2570.2]

/-- Complete interval computation for depth 12, residue 2571. -/
theorem bounds_12_2571 : exactInterval 12 2571 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2571 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2571) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2571 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2571 : oddCount 2571 12 = 7 ∧ acceleratedOrbit 12 2571 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2571 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2571) = 3 ^ 7 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2571.1, data_12_2571.2]

/-- Complete interval computation for depth 12, residue 2572. -/
theorem bounds_12_2572 : exactInterval 12 2572 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2572 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2572) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2572 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2572 : oddCount 2572 12 = 3 ∧ acceleratedOrbit 12 2572 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2572 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2572) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2572.1, data_12_2572.2]

/-- Complete interval computation for depth 12, residue 2573. -/
theorem bounds_12_2573 : exactInterval 12 2573 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2573 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2573) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2573 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2573 : oddCount 2573 12 = 3 ∧ acceleratedOrbit 12 2573 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2573 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2573) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2573.1, data_12_2573.2]

/-- Complete interval computation for depth 12, residue 2574. -/
theorem bounds_12_2574 : exactInterval 12 2574 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2574 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2574) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2574 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2574 : oddCount 2574 12 = 8 ∧ acceleratedOrbit 12 2574 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2574 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2574) = 3 ^ 8 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2574.1, data_12_2574.2]

/-- Complete interval computation for depth 12, residue 2575. -/
theorem bounds_12_2575 : exactInterval 12 2575 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2575 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2575) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2575 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2575 : oddCount 2575 12 = 8 ∧ acceleratedOrbit 12 2575 = 4130 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2575 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2575) = 3 ^ 8 * m + 4130 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2575.1, data_12_2575.2]

/-- Complete interval computation for depth 12, residue 2576. -/
theorem bounds_12_2576 : exactInterval 12 2576 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2576 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2576) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2576 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2576 : oddCount 2576 12 = 5 ∧ acceleratedOrbit 12 2576 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2576 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2576) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2576.1, data_12_2576.2]

/-- Complete interval computation for depth 12, residue 2577. -/
theorem bounds_12_2577 : exactInterval 12 2577 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2577 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2577) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2577 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2577 : oddCount 2577 12 = 3 ∧ acceleratedOrbit 12 2577 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2577 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2577) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2577.1, data_12_2577.2]

/-- Complete interval computation for depth 12, residue 2578. -/
theorem bounds_12_2578 : exactInterval 12 2578 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2578 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2578) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2578 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2578 : oddCount 2578 12 = 7 ∧ acceleratedOrbit 12 2578 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2578 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2578) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2578.1, data_12_2578.2]

/-- Complete interval computation for depth 12, residue 2579. -/
theorem bounds_12_2579 : exactInterval 12 2579 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2579 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2579) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2579 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2579 : oddCount 2579 12 = 7 ∧ acceleratedOrbit 12 2579 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2579 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2579) = 3 ^ 7 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2579.1, data_12_2579.2]

end Collatz.Research.StoppingAtlas.Batch0368
