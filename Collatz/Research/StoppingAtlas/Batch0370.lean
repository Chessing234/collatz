import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0370

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2595. -/
theorem bounds_12_2595 : exactInterval 12 2595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2595 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2595) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2595 : oddCount 2595 12 = 5 ∧ acceleratedOrbit 12 2595 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2595 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2595) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2595.1, data_12_2595.2]

/-- Complete interval computation for depth 12, residue 2596. -/
theorem bounds_12_2596 : exactInterval 12 2596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2596 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2596) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2596 : oddCount 2596 12 = 7 ∧ acceleratedOrbit 12 2596 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2596 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2596) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2596.1, data_12_2596.2]

/-- Complete interval computation for depth 12, residue 2597. -/
theorem bounds_12_2597 : exactInterval 12 2597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2597 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2597) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2597 : oddCount 2597 12 = 7 ∧ acceleratedOrbit 12 2597 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2597 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2597) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2597.1, data_12_2597.2]

/-- Complete interval computation for depth 12, residue 2598. -/
theorem bounds_12_2598 : exactInterval 12 2598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2598 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2598) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2598 : oddCount 2598 12 = 7 ∧ acceleratedOrbit 12 2598 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2598 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2598) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2598.1, data_12_2598.2]

/-- Complete interval computation for depth 12, residue 2599. -/
theorem bounds_12_2599 : exactInterval 12 2599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2599 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2599) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2599 : oddCount 2599 12 = 6 ∧ acceleratedOrbit 12 2599 = 463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2599 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2599) = 3 ^ 6 * m + 463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2599.1, data_12_2599.2]

/-- Complete interval computation for depth 12, residue 2600. -/
theorem bounds_12_2600 : exactInterval 12 2600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2600 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2600) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2600 : oddCount 2600 12 = 4 ∧ acceleratedOrbit 12 2600 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2600 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2600) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2600.1, data_12_2600.2]

/-- Complete interval computation for depth 12, residue 2601. -/
theorem bounds_12_2601 : exactInterval 12 2601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2601 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2601) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2601 : oddCount 2601 12 = 8 ∧ acceleratedOrbit 12 2601 = 4169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2601 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2601) = 3 ^ 8 * m + 4169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2601.1, data_12_2601.2]

/-- Complete interval computation for depth 12, residue 2602. -/
theorem bounds_12_2602 : exactInterval 12 2602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2602 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2602) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2602 : oddCount 2602 12 = 4 ∧ acceleratedOrbit 12 2602 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2602 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2602) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2602.1, data_12_2602.2]

/-- Complete interval computation for depth 12, residue 2603. -/
theorem bounds_12_2603 : exactInterval 12 2603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2603 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2603) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2603 : oddCount 2603 12 = 5 ∧ acceleratedOrbit 12 2603 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2603 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2603) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2603.1, data_12_2603.2]

/-- Complete interval computation for depth 12, residue 2604. -/
theorem bounds_12_2604 : exactInterval 12 2604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2604 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2604) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2604 : oddCount 2604 12 = 5 ∧ acceleratedOrbit 12 2604 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2604 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2604) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2604.1, data_12_2604.2]

/-- Complete interval computation for depth 12, residue 2605. -/
theorem bounds_12_2605 : exactInterval 12 2605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2605 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2605) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2605 : oddCount 2605 12 = 5 ∧ acceleratedOrbit 12 2605 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2605 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2605) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2605.1, data_12_2605.2]

/-- Complete interval computation for depth 12, residue 2606. -/
theorem bounds_12_2606 : exactInterval 12 2606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2606 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2606) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2606 : oddCount 2606 12 = 5 ∧ acceleratedOrbit 12 2606 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2606 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2606) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2606.1, data_12_2606.2]

/-- Complete interval computation for depth 12, residue 2607. -/
theorem bounds_12_2607 : exactInterval 12 2607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2607 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2607) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2607 : oddCount 2607 12 = 8 ∧ acceleratedOrbit 12 2607 = 4178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2607 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2607) = 3 ^ 8 * m + 4178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2607.1, data_12_2607.2]

/-- Complete interval computation for depth 12, residue 2608. -/
theorem bounds_12_2608 : exactInterval 12 2608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2608 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2608) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2608 : oddCount 2608 12 = 4 ∧ acceleratedOrbit 12 2608 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2608 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2608) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2608.1, data_12_2608.2]

/-- Complete interval computation for depth 12, residue 2609. -/
theorem bounds_12_2609 : exactInterval 12 2609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2609 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2609) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2609 : oddCount 2609 12 = 7 ∧ acceleratedOrbit 12 2609 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2609 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2609) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2609.1, data_12_2609.2]

/-- Complete interval computation for depth 12, residue 2610. -/
theorem bounds_12_2610 : exactInterval 12 2610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2610 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2610) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2610 : oddCount 2610 12 = 7 ∧ acceleratedOrbit 12 2610 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2610 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2610) = 3 ^ 7 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2610.1, data_12_2610.2]

end Collatz.Research.StoppingAtlas.Batch0370
