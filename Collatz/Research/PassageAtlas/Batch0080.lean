import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0080

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2588. -/
theorem bounds_15_2588 : exactInterval 15 2588 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2588 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2588) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2588 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2588 : oddCount 2588 15 = 6 ∧ acceleratedOrbit 15 2588 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2588 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2588) = 3 ^ 6 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2588.1, data_15_2588.2]

/-- Complete interval computation for depth 15, residue 2589. -/
theorem bounds_15_2589 : exactInterval 15 2589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2589 : oddCount 2589 15 = 6 ∧ acceleratedOrbit 15 2589 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2589) = 3 ^ 6 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2589.1, data_15_2589.2]

/-- Complete interval computation for depth 15, residue 2590. -/
theorem bounds_15_2590 : exactInterval 15 2590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2590 : oddCount 2590 15 = 6 ∧ acceleratedOrbit 15 2590 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2590) = 3 ^ 6 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2590.1, data_15_2590.2]

/-- Complete interval computation for depth 15, residue 2591. -/
theorem bounds_15_2591 : exactInterval 15 2591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2591 : oddCount 2591 15 = 7 ∧ acceleratedOrbit 15 2591 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2591) = 3 ^ 7 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2591.1, data_15_2591.2]

/-- Complete interval computation for depth 15, residue 2592. -/
theorem bounds_15_2592 : exactInterval 15 2592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2592 : oddCount 2592 15 = 5 ∧ acceleratedOrbit 15 2592 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2592) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2592.1, data_15_2592.2]

/-- Complete interval computation for depth 15, residue 2593. -/
theorem bounds_15_2593 : exactInterval 15 2593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2593 : oddCount 2593 15 = 6 ∧ acceleratedOrbit 15 2593 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2593) = 3 ^ 6 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2593.1, data_15_2593.2]

/-- Complete interval computation for depth 15, residue 2594. -/
theorem bounds_15_2594 : exactInterval 15 2594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2594 : oddCount 2594 15 = 7 ∧ acceleratedOrbit 15 2594 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2594) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2594.1, data_15_2594.2]

/-- Complete interval computation for depth 15, residue 2595. -/
theorem bounds_15_2595 : exactInterval 15 2595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2595 : oddCount 2595 15 = 7 ∧ acceleratedOrbit 15 2595 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2595) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2595.1, data_15_2595.2]

/-- Complete interval computation for depth 15, residue 2596. -/
theorem bounds_15_2596 : exactInterval 15 2596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2596 : oddCount 2596 15 = 9 ∧ acceleratedOrbit 15 2596 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2596) = 3 ^ 9 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2596.1, data_15_2596.2]

/-- Complete interval computation for depth 15, residue 2597. -/
theorem bounds_15_2597 : exactInterval 15 2597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2597 : oddCount 2597 15 = 9 ∧ acceleratedOrbit 15 2597 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2597) = 3 ^ 9 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2597.1, data_15_2597.2]

/-- Complete interval computation for depth 15, residue 2598. -/
theorem bounds_15_2598 : exactInterval 15 2598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2598 : oddCount 2598 15 = 9 ∧ acceleratedOrbit 15 2598 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2598) = 3 ^ 9 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2598.1, data_15_2598.2]

/-- Complete interval computation for depth 15, residue 2599. -/
theorem bounds_15_2599 : exactInterval 15 2599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2599 : oddCount 2599 15 = 9 ∧ acceleratedOrbit 15 2599 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2599) = 3 ^ 9 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2599.1, data_15_2599.2]

/-- Complete interval computation for depth 15, residue 2600. -/
theorem bounds_15_2600 : exactInterval 15 2600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2600 : oddCount 2600 15 = 5 ∧ acceleratedOrbit 15 2600 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2600) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2600.1, data_15_2600.2]

/-- Complete interval computation for depth 15, residue 2601. -/
theorem bounds_15_2601 : exactInterval 15 2601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2601 : oddCount 2601 15 = 10 ∧ acceleratedOrbit 15 2601 = 4691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2601) = 3 ^ 10 * m + 4691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2601.1, data_15_2601.2]

/-- Complete interval computation for depth 15, residue 2602. -/
theorem bounds_15_2602 : exactInterval 15 2602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2602 : oddCount 2602 15 = 5 ∧ acceleratedOrbit 15 2602 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2602) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2602.1, data_15_2602.2]

/-- Complete interval computation for depth 15, residue 2603. -/
theorem bounds_15_2603 : exactInterval 15 2603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2603 : oddCount 2603 15 = 7 ∧ acceleratedOrbit 15 2603 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2603) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2603.1, data_15_2603.2]

/-- Complete interval computation for depth 15, residue 2604. -/
theorem bounds_15_2604 : exactInterval 15 2604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2604 : oddCount 2604 15 = 7 ∧ acceleratedOrbit 15 2604 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2604) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2604.1, data_15_2604.2]

/-- Complete interval computation for depth 15, residue 2605. -/
theorem bounds_15_2605 : exactInterval 15 2605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2605 : oddCount 2605 15 = 7 ∧ acceleratedOrbit 15 2605 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2605) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2605.1, data_15_2605.2]

/-- Complete interval computation for depth 15, residue 2606. -/
theorem bounds_15_2606 : exactInterval 15 2606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2606 : oddCount 2606 15 = 7 ∧ acceleratedOrbit 15 2606 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2606) = 3 ^ 7 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2606.1, data_15_2606.2]

/-- Complete interval computation for depth 15, residue 2607. -/
theorem bounds_15_2607 : exactInterval 15 2607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2607 : oddCount 2607 15 = 9 ∧ acceleratedOrbit 15 2607 = 1567 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2607) = 3 ^ 9 * m + 1567 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2607.1, data_15_2607.2]

/-- Complete interval computation for depth 15, residue 2608. -/
theorem bounds_15_2608 : exactInterval 15 2608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2608 : oddCount 2608 15 = 5 ∧ acceleratedOrbit 15 2608 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2608) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2608.1, data_15_2608.2]

/-- Complete interval computation for depth 15, residue 2609. -/
theorem bounds_15_2609 : exactInterval 15 2609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2609 : oddCount 2609 15 = 8 ∧ acceleratedOrbit 15 2609 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2609) = 3 ^ 8 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2609.1, data_15_2609.2]

/-- Complete interval computation for depth 15, residue 2610. -/
theorem bounds_15_2610 : exactInterval 15 2610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2610 : oddCount 2610 15 = 8 ∧ acceleratedOrbit 15 2610 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2610) = 3 ^ 8 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2610.1, data_15_2610.2]

/-- Complete interval computation for depth 15, residue 2611. -/
theorem bounds_15_2611 : exactInterval 15 2611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2611 : oddCount 2611 15 = 8 ∧ acceleratedOrbit 15 2611 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2611) = 3 ^ 8 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2611.1, data_15_2611.2]

/-- Complete interval computation for depth 15, residue 2612. -/
theorem bounds_15_2612 : exactInterval 15 2612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2612 : oddCount 2612 15 = 5 ∧ acceleratedOrbit 15 2612 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2612) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2612.1, data_15_2612.2]

/-- Complete interval computation for depth 15, residue 2613. -/
theorem bounds_15_2613 : exactInterval 15 2613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2613 : oddCount 2613 15 = 5 ∧ acceleratedOrbit 15 2613 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2613) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2613.1, data_15_2613.2]

/-- Complete interval computation for depth 15, residue 2614. -/
theorem bounds_15_2614 : exactInterval 15 2614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2614 : oddCount 2614 15 = 12 ∧ acceleratedOrbit 15 2614 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2614) = 3 ^ 12 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2614.1, data_15_2614.2]

/-- Complete interval computation for depth 15, residue 2615. -/
theorem bounds_15_2615 : exactInterval 15 2615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2615 : oddCount 2615 15 = 12 ∧ acceleratedOrbit 15 2615 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2615) = 3 ^ 12 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2615.1, data_15_2615.2]

/-- Complete interval computation for depth 15, residue 2616. -/
theorem bounds_15_2616 : exactInterval 15 2616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2616 : oddCount 2616 15 = 9 ∧ acceleratedOrbit 15 2616 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2616) = 3 ^ 9 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2616.1, data_15_2616.2]

/-- Complete interval computation for depth 15, residue 2617. -/
theorem bounds_15_2617 : exactInterval 15 2617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2617 : oddCount 2617 15 = 10 ∧ acceleratedOrbit 15 2617 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2617) = 3 ^ 10 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2617.1, data_15_2617.2]

/-- Complete interval computation for depth 15, residue 2618. -/
theorem bounds_15_2618 : exactInterval 15 2618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2618 : oddCount 2618 15 = 9 ∧ acceleratedOrbit 15 2618 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2618) = 3 ^ 9 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2618.1, data_15_2618.2]

/-- Complete interval computation for depth 15, residue 2619. -/
theorem bounds_15_2619 : exactInterval 15 2619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2619 : oddCount 2619 15 = 8 ∧ acceleratedOrbit 15 2619 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2619) = 3 ^ 8 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2619.1, data_15_2619.2]

/-- Complete interval computation for depth 15, residue 2620. -/
theorem bounds_15_2620 : exactInterval 15 2620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2620 : oddCount 2620 15 = 9 ∧ acceleratedOrbit 15 2620 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2620) = 3 ^ 9 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2620.1, data_15_2620.2]

end Collatz.Research.PassageAtlas.Batch0080
