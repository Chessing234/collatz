import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0507

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 604. -/
theorem bounds_13_604 : exactInterval 13 604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_604 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 604) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_604 : oddCount 604 13 = 3 ∧ acceleratedOrbit 13 604 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_604 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 604) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_604.1, data_13_604.2]

/-- Complete interval computation for depth 13, residue 605. -/
theorem bounds_13_605 : exactInterval 13 605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_605 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 605) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_605 : oddCount 605 13 = 3 ∧ acceleratedOrbit 13 605 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_605 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 605) = 3 ^ 3 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_605.1, data_13_605.2]

/-- Complete interval computation for depth 13, residue 606. -/
theorem bounds_13_606 : exactInterval 13 606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_606 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 606) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_606 : oddCount 606 13 = 8 ∧ acceleratedOrbit 13 606 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_606 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 606) = 3 ^ 8 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_606.1, data_13_606.2]

/-- Complete interval computation for depth 13, residue 607. -/
theorem bounds_13_607 : exactInterval 13 607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_607 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 607) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_607 : oddCount 607 13 = 8 ∧ acceleratedOrbit 13 607 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_607 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 607) = 3 ^ 8 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_607.1, data_13_607.2]

/-- Complete interval computation for depth 13, residue 608. -/
theorem bounds_13_608 : exactInterval 13 608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_608 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 608) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_608 : oddCount 608 13 = 5 ∧ acceleratedOrbit 13 608 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_608 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 608) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_608.1, data_13_608.2]

/-- Complete interval computation for depth 13, residue 609. -/
theorem bounds_13_609 : exactInterval 13 609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_609 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 609) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_609 : oddCount 609 13 = 7 ∧ acceleratedOrbit 13 609 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_609 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 609) = 3 ^ 7 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_609.1, data_13_609.2]

/-- Complete interval computation for depth 13, residue 610. -/
theorem bounds_13_610 : exactInterval 13 610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_610 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 610) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_610 : oddCount 610 13 = 6 ∧ acceleratedOrbit 13 610 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_610 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 610) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_610.1, data_13_610.2]

/-- Complete interval computation for depth 13, residue 611. -/
theorem bounds_13_611 : exactInterval 13 611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_611 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 611) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_611 : oddCount 611 13 = 6 ∧ acceleratedOrbit 13 611 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_611 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 611) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_611.1, data_13_611.2]

/-- Complete interval computation for depth 13, residue 612. -/
theorem bounds_13_612 : exactInterval 13 612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_612 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 612) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_612 : oddCount 612 13 = 6 ∧ acceleratedOrbit 13 612 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_612 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 612) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_612.1, data_13_612.2]

/-- Complete interval computation for depth 13, residue 613. -/
theorem bounds_13_613 : exactInterval 13 613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_613 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 613) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_613 : oddCount 613 13 = 6 ∧ acceleratedOrbit 13 613 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_613 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 613) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_613.1, data_13_613.2]

/-- Complete interval computation for depth 13, residue 614. -/
theorem bounds_13_614 : exactInterval 13 614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_614 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 614) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_614 : oddCount 614 13 = 6 ∧ acceleratedOrbit 13 614 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_614 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 614) = 3 ^ 6 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_614.1, data_13_614.2]

/-- Complete interval computation for depth 13, residue 615. -/
theorem bounds_13_615 : exactInterval 13 615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_615 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 615) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_615 : oddCount 615 13 = 8 ∧ acceleratedOrbit 13 615 = 494 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_615 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 615) = 3 ^ 8 * m + 494 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_615.1, data_13_615.2]

/-- Complete interval computation for depth 13, residue 616. -/
theorem bounds_13_616 : exactInterval 13 616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_616 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 616) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_616 : oddCount 616 13 = 5 ∧ acceleratedOrbit 13 616 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_616 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 616) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_616.1, data_13_616.2]

/-- Complete interval computation for depth 13, residue 617. -/
theorem bounds_13_617 : exactInterval 13 617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_617 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 617) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_617 : oddCount 617 13 = 8 ∧ acceleratedOrbit 13 617 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_617 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 617) = 3 ^ 8 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_617.1, data_13_617.2]

/-- Complete interval computation for depth 13, residue 618. -/
theorem bounds_13_618 : exactInterval 13 618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_618 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 618) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_618 : oddCount 618 13 = 5 ∧ acceleratedOrbit 13 618 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_618 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 618) = 3 ^ 5 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_618.1, data_13_618.2]

end Collatz.Research.StoppingAtlas.Batch0507
