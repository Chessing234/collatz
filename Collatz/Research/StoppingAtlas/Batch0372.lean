import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0372

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2626. -/
theorem bounds_12_2626 : exactInterval 12 2626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2626 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2626) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2626 : oddCount 2626 12 = 4 ∧ acceleratedOrbit 12 2626 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2626 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2626) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2626.1, data_12_2626.2]

/-- Complete interval computation for depth 12, residue 2627. -/
theorem bounds_12_2627 : exactInterval 12 2627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2627 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2627) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2627 : oddCount 2627 12 = 4 ∧ acceleratedOrbit 12 2627 = 52 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2627 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2627) = 3 ^ 4 * m + 52 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2627.1, data_12_2627.2]

/-- Complete interval computation for depth 12, residue 2628. -/
theorem bounds_12_2628 : exactInterval 12 2628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2628 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2628) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2628 : oddCount 2628 12 = 5 ∧ acceleratedOrbit 12 2628 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2628 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2628) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2628.1, data_12_2628.2]

/-- Complete interval computation for depth 12, residue 2629. -/
theorem bounds_12_2629 : exactInterval 12 2629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2629 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2629) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2629 : oddCount 2629 12 = 5 ∧ acceleratedOrbit 12 2629 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2629 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2629) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2629.1, data_12_2629.2]

/-- Complete interval computation for depth 12, residue 2630. -/
theorem bounds_12_2630 : exactInterval 12 2630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2630 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2630) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2630 : oddCount 2630 12 = 5 ∧ acceleratedOrbit 12 2630 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2630 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2630) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2630.1, data_12_2630.2]

/-- Complete interval computation for depth 12, residue 2631. -/
theorem bounds_12_2631 : exactInterval 12 2631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2631 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2631) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2631 : oddCount 2631 12 = 7 ∧ acceleratedOrbit 12 2631 = 1406 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2631 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2631) = 3 ^ 7 * m + 1406 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2631.1, data_12_2631.2]

/-- Complete interval computation for depth 12, residue 2632. -/
theorem bounds_12_2632 : exactInterval 12 2632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2632 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2632) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2632 : oddCount 2632 12 = 5 ∧ acceleratedOrbit 12 2632 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2632 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2632) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2632.1, data_12_2632.2]

/-- Complete interval computation for depth 12, residue 2633. -/
theorem bounds_12_2633 : exactInterval 12 2633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2633 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2633) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2633 : oddCount 2633 12 = 6 ∧ acceleratedOrbit 12 2633 = 469 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2633 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2633) = 3 ^ 6 * m + 469 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2633.1, data_12_2633.2]

/-- Complete interval computation for depth 12, residue 2634. -/
theorem bounds_12_2634 : exactInterval 12 2634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2634 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2634) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2634 : oddCount 2634 12 = 5 ∧ acceleratedOrbit 12 2634 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2634 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2634) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2634.1, data_12_2634.2]

/-- Complete interval computation for depth 12, residue 2635. -/
theorem bounds_12_2635 : exactInterval 12 2635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2635 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2635) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2635 : oddCount 2635 12 = 5 ∧ acceleratedOrbit 12 2635 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2635 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2635) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2635.1, data_12_2635.2]

/-- Complete interval computation for depth 12, residue 2636. -/
theorem bounds_12_2636 : exactInterval 12 2636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2636 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2636) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2636 : oddCount 2636 12 = 5 ∧ acceleratedOrbit 12 2636 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2636 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2636) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2636.1, data_12_2636.2]

/-- Complete interval computation for depth 12, residue 2637. -/
theorem bounds_12_2637 : exactInterval 12 2637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2637 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2637) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2637 : oddCount 2637 12 = 5 ∧ acceleratedOrbit 12 2637 = 157 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2637 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2637) = 3 ^ 5 * m + 157 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2637.1, data_12_2637.2]

/-- Complete interval computation for depth 12, residue 2638. -/
theorem bounds_12_2638 : exactInterval 12 2638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2638 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2638) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2638 : oddCount 2638 12 = 6 ∧ acceleratedOrbit 12 2638 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2638 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2638) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2638.1, data_12_2638.2]

/-- Complete interval computation for depth 12, residue 2639. -/
theorem bounds_12_2639 : exactInterval 12 2639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2639 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2639) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2639 : oddCount 2639 12 = 6 ∧ acceleratedOrbit 12 2639 = 470 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2639 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2639) = 3 ^ 6 * m + 470 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2639.1, data_12_2639.2]

/-- Complete interval computation for depth 12, residue 2640. -/
theorem bounds_12_2640 : exactInterval 12 2640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2640 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2640) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2640 : oddCount 2640 12 = 5 ∧ acceleratedOrbit 12 2640 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2640 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2640) = 3 ^ 5 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2640.1, data_12_2640.2]

end Collatz.Research.StoppingAtlas.Batch0372
