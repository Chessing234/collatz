import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0107

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 604. -/
theorem bounds_11_604 : exactInterval 11 604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_604 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 604) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_604 : oddCount 604 11 = 3 ∧ acceleratedOrbit 11 604 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_604 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 604) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_604.1, data_11_604.2]

/-- Complete interval computation for depth 11, residue 605. -/
theorem bounds_11_605 : exactInterval 11 605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_605 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 605) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_605 : oddCount 605 11 = 3 ∧ acceleratedOrbit 11 605 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_605 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 605) = 3 ^ 3 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_605.1, data_11_605.2]

/-- Complete interval computation for depth 11, residue 606. -/
theorem bounds_11_606 : exactInterval 11 606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_606 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 606) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_606 : oddCount 606 11 = 7 ∧ acceleratedOrbit 11 606 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_606 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 606) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_606.1, data_11_606.2]

/-- Complete interval computation for depth 11, residue 607. -/
theorem bounds_11_607 : exactInterval 11 607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_607 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 607) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_607 : oddCount 607 11 = 7 ∧ acceleratedOrbit 11 607 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_607 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 607) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_607.1, data_11_607.2]

/-- Complete interval computation for depth 11, residue 608. -/
theorem bounds_11_608 : exactInterval 11 608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_608 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 608) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_608 : oddCount 608 11 = 4 ∧ acceleratedOrbit 11 608 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_608 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 608) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_608.1, data_11_608.2]

/-- Complete interval computation for depth 11, residue 609. -/
theorem bounds_11_609 : exactInterval 11 609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_609 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 609) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_609 : oddCount 609 11 = 6 ∧ acceleratedOrbit 11 609 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_609 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 609) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_609.1, data_11_609.2]

/-- Complete interval computation for depth 11, residue 610. -/
theorem bounds_11_610 : exactInterval 11 610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_610 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 610) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_610 : oddCount 610 11 = 5 ∧ acceleratedOrbit 11 610 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_610 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 610) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_610.1, data_11_610.2]

/-- Complete interval computation for depth 11, residue 611. -/
theorem bounds_11_611 : exactInterval 11 611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_611 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 611) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_611 : oddCount 611 11 = 5 ∧ acceleratedOrbit 11 611 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_611 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 611) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_611.1, data_11_611.2]

/-- Complete interval computation for depth 11, residue 612. -/
theorem bounds_11_612 : exactInterval 11 612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_612 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 612) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_612 : oddCount 612 11 = 5 ∧ acceleratedOrbit 11 612 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_612 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 612) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_612.1, data_11_612.2]

/-- Complete interval computation for depth 11, residue 613. -/
theorem bounds_11_613 : exactInterval 11 613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_613 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 613) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_613 : oddCount 613 11 = 5 ∧ acceleratedOrbit 11 613 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_613 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 613) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_613.1, data_11_613.2]

/-- Complete interval computation for depth 11, residue 614. -/
theorem bounds_11_614 : exactInterval 11 614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_614 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 614) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_614 : oddCount 614 11 = 5 ∧ acceleratedOrbit 11 614 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_614 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 614) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_614.1, data_11_614.2]

/-- Complete interval computation for depth 11, residue 615. -/
theorem bounds_11_615 : exactInterval 11 615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_615 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 615) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_615 : oddCount 615 11 = 7 ∧ acceleratedOrbit 11 615 = 658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_615 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 615) = 3 ^ 7 * m + 658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_615.1, data_11_615.2]

/-- Complete interval computation for depth 11, residue 616. -/
theorem bounds_11_616 : exactInterval 11 616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_616 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 616) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_616 : oddCount 616 11 = 4 ∧ acceleratedOrbit 11 616 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_616 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 616) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_616.1, data_11_616.2]

/-- Complete interval computation for depth 11, residue 617. -/
theorem bounds_11_617 : exactInterval 11 617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_617 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 617) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_617 : oddCount 617 11 = 7 ∧ acceleratedOrbit 11 617 = 661 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_617 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 617) = 3 ^ 7 * m + 661 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_617.1, data_11_617.2]

/-- Complete interval computation for depth 11, residue 618. -/
theorem bounds_11_618 : exactInterval 11 618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_618 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 618) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_618 : oddCount 618 11 = 4 ∧ acceleratedOrbit 11 618 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_618 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 618) = 3 ^ 4 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_618.1, data_11_618.2]

end Collatz.Research.StoppingAtlas.Batch0107
