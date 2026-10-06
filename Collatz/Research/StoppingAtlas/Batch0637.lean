import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0637

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2600. -/
theorem bounds_13_2600 : exactInterval 13 2600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2600 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2600) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2600 : oddCount 2600 13 = 5 ∧ acceleratedOrbit 13 2600 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2600 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2600) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2600.1, data_13_2600.2]

/-- Complete interval computation for depth 13, residue 2601. -/
theorem bounds_13_2601 : exactInterval 13 2601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2601 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2601) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2601 : oddCount 2601 13 = 9 ∧ acceleratedOrbit 13 2601 = 6254 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2601 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2601) = 3 ^ 9 * m + 6254 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2601.1, data_13_2601.2]

/-- Complete interval computation for depth 13, residue 2602. -/
theorem bounds_13_2602 : exactInterval 13 2602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2602 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2602) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2602 : oddCount 2602 13 = 5 ∧ acceleratedOrbit 13 2602 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2602 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2602) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2602.1, data_13_2602.2]

/-- Complete interval computation for depth 13, residue 2603. -/
theorem bounds_13_2603 : exactInterval 13 2603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2603 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2603) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2603 : oddCount 2603 13 = 6 ∧ acceleratedOrbit 13 2603 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2603 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2603) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2603.1, data_13_2603.2]

/-- Complete interval computation for depth 13, residue 2604. -/
theorem bounds_13_2604 : exactInterval 13 2604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2604 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2604) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2604 : oddCount 2604 13 = 6 ∧ acceleratedOrbit 13 2604 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2604 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2604) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2604.1, data_13_2604.2]

/-- Complete interval computation for depth 13, residue 2605. -/
theorem bounds_13_2605 : exactInterval 13 2605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2605 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2605) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2605 : oddCount 2605 13 = 6 ∧ acceleratedOrbit 13 2605 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2605 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2605) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2605.1, data_13_2605.2]

/-- Complete interval computation for depth 13, residue 2606. -/
theorem bounds_13_2606 : exactInterval 13 2606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2606 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2606) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2606 : oddCount 2606 13 = 6 ∧ acceleratedOrbit 13 2606 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2606 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2606) = 3 ^ 6 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2606.1, data_13_2606.2]

/-- Complete interval computation for depth 13, residue 2607. -/
theorem bounds_13_2607 : exactInterval 13 2607 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2607 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2607) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2607 : oddCount 2607 13 = 8 ∧ acceleratedOrbit 13 2607 = 2089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2607 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2607) = 3 ^ 8 * m + 2089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2607.1, data_13_2607.2]

/-- Complete interval computation for depth 13, residue 2608. -/
theorem bounds_13_2608 : exactInterval 13 2608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2608 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2608) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2608 : oddCount 2608 13 = 5 ∧ acceleratedOrbit 13 2608 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2608 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2608) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2608.1, data_13_2608.2]

/-- Complete interval computation for depth 13, residue 2609. -/
theorem bounds_13_2609 : exactInterval 13 2609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2609 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2609) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2609 : oddCount 2609 13 = 8 ∧ acceleratedOrbit 13 2609 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2609 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2609) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2609.1, data_13_2609.2]

/-- Complete interval computation for depth 13, residue 2610. -/
theorem bounds_13_2610 : exactInterval 13 2610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2610 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2610) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2610 : oddCount 2610 13 = 8 ∧ acceleratedOrbit 13 2610 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2610 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2610) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2610.1, data_13_2610.2]

/-- Complete interval computation for depth 13, residue 2611. -/
theorem bounds_13_2611 : exactInterval 13 2611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2611 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2611) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2611 : oddCount 2611 13 = 8 ∧ acceleratedOrbit 13 2611 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2611 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2611) = 3 ^ 8 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2611.1, data_13_2611.2]

/-- Complete interval computation for depth 13, residue 2612. -/
theorem bounds_13_2612 : exactInterval 13 2612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2612 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2612) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2612 : oddCount 2612 13 = 5 ∧ acceleratedOrbit 13 2612 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2612 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2612) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2612.1, data_13_2612.2]

/-- Complete interval computation for depth 13, residue 2613. -/
theorem bounds_13_2613 : exactInterval 13 2613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2613 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2613) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2613 : oddCount 2613 13 = 5 ∧ acceleratedOrbit 13 2613 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2613 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2613) = 3 ^ 5 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2613.1, data_13_2613.2]

/-- Complete interval computation for depth 13, residue 2614. -/
theorem bounds_13_2614 : exactInterval 13 2614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2614 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2614) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2614 : oddCount 2614 13 = 10 ∧ acceleratedOrbit 13 2614 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2614 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2614) = 3 ^ 10 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2614.1, data_13_2614.2]

/-- Complete interval computation for depth 13, residue 2615. -/
theorem bounds_13_2615 : exactInterval 13 2615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2615 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2615) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2615 : oddCount 2615 13 = 10 ∧ acceleratedOrbit 13 2615 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2615 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2615) = 3 ^ 10 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2615.1, data_13_2615.2]

end Collatz.Research.StoppingAtlas.Batch0637
