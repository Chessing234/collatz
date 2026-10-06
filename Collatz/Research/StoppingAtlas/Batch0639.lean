import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0639

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2631. -/
theorem bounds_13_2631 : exactInterval 13 2631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2631 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2631) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2631 : oddCount 2631 13 = 7 ∧ acceleratedOrbit 13 2631 = 703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2631 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2631) = 3 ^ 7 * m + 703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2631.1, data_13_2631.2]

/-- Complete interval computation for depth 13, residue 2632. -/
theorem bounds_13_2632 : exactInterval 13 2632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2632 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2632) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2632 : oddCount 2632 13 = 6 ∧ acceleratedOrbit 13 2632 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2632 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2632) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2632.1, data_13_2632.2]

/-- Complete interval computation for depth 13, residue 2633. -/
theorem bounds_13_2633 : exactInterval 13 2633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2633 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2633) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2633 : oddCount 2633 13 = 7 ∧ acceleratedOrbit 13 2633 = 704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2633 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2633) = 3 ^ 7 * m + 704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2633.1, data_13_2633.2]

/-- Complete interval computation for depth 13, residue 2634. -/
theorem bounds_13_2634 : exactInterval 13 2634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2634 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2634) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2634 : oddCount 2634 13 = 6 ∧ acceleratedOrbit 13 2634 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2634 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2634) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2634.1, data_13_2634.2]

/-- Complete interval computation for depth 13, residue 2635. -/
theorem bounds_13_2635 : exactInterval 13 2635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2635 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2635) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2635 : oddCount 2635 13 = 6 ∧ acceleratedOrbit 13 2635 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2635 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2635) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2635.1, data_13_2635.2]

/-- Complete interval computation for depth 13, residue 2636. -/
theorem bounds_13_2636 : exactInterval 13 2636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2636 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2636) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2636 : oddCount 2636 13 = 6 ∧ acceleratedOrbit 13 2636 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2636 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2636) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2636.1, data_13_2636.2]

/-- Complete interval computation for depth 13, residue 2637. -/
theorem bounds_13_2637 : exactInterval 13 2637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2637 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2637) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2637 : oddCount 2637 13 = 6 ∧ acceleratedOrbit 13 2637 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2637 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2637) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2637.1, data_13_2637.2]

/-- Complete interval computation for depth 13, residue 2638. -/
theorem bounds_13_2638 : exactInterval 13 2638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2638 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2638) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2638 : oddCount 2638 13 = 6 ∧ acceleratedOrbit 13 2638 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2638 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2638) = 3 ^ 6 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2638.1, data_13_2638.2]

/-- Complete interval computation for depth 13, residue 2639. -/
theorem bounds_13_2639 : exactInterval 13 2639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2639 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2639) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2639 : oddCount 2639 13 = 6 ∧ acceleratedOrbit 13 2639 = 235 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2639 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2639) = 3 ^ 6 * m + 235 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2639.1, data_13_2639.2]

/-- Complete interval computation for depth 13, residue 2640. -/
theorem bounds_13_2640 : exactInterval 13 2640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2640 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2640) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2640 : oddCount 2640 13 = 6 ∧ acceleratedOrbit 13 2640 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2640 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2640) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2640.1, data_13_2640.2]

/-- Complete interval computation for depth 13, residue 2641. -/
theorem bounds_13_2641 : exactInterval 13 2641 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2641 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2641) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2641 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2641 : oddCount 2641 13 = 8 ∧ acceleratedOrbit 13 2641 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2641 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2641) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2641.1, data_13_2641.2]

/-- Complete interval computation for depth 13, residue 2642. -/
theorem bounds_13_2642 : exactInterval 13 2642 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2642 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2642) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2642 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2642 : oddCount 2642 13 = 8 ∧ acceleratedOrbit 13 2642 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2642 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2642) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2642.1, data_13_2642.2]

/-- Complete interval computation for depth 13, residue 2643. -/
theorem bounds_13_2643 : exactInterval 13 2643 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2643 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2643) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2643 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2643 : oddCount 2643 13 = 8 ∧ acceleratedOrbit 13 2643 = 2119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2643 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2643) = 3 ^ 8 * m + 2119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2643.1, data_13_2643.2]

/-- Complete interval computation for depth 13, residue 2644. -/
theorem bounds_13_2644 : exactInterval 13 2644 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2644 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2644) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2644 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2644 : oddCount 2644 13 = 6 ∧ acceleratedOrbit 13 2644 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2644 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2644) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2644.1, data_13_2644.2]

/-- Complete interval computation for depth 13, residue 2645. -/
theorem bounds_13_2645 : exactInterval 13 2645 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2645 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2645) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2645 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2645 : oddCount 2645 13 = 6 ∧ acceleratedOrbit 13 2645 = 242 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2645 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2645) = 3 ^ 6 * m + 242 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2645.1, data_13_2645.2]

/-- Complete interval computation for depth 13, residue 2646. -/
theorem bounds_13_2646 : exactInterval 13 2646 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2646 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2646) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2646 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2646 : oddCount 2646 13 = 6 ∧ acceleratedOrbit 13 2646 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2646 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2646) = 3 ^ 6 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2646.1, data_13_2646.2]

end Collatz.Research.StoppingAtlas.Batch0639
