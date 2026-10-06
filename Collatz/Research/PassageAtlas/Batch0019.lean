import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0019

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 589. -/
theorem bounds_15_589 : exactInterval 15 589 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_589 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 589) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_589 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_589 : oddCount 589 15 = 8 ∧ acceleratedOrbit 15 589 = 121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_589 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 589) = 3 ^ 8 * m + 121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_589.1, data_15_589.2]

/-- Complete interval computation for depth 15, residue 590. -/
theorem bounds_15_590 : exactInterval 15 590 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_590 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 590) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_590 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_590 : oddCount 590 15 = 8 ∧ acceleratedOrbit 15 590 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_590 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 590) = 3 ^ 8 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_590.1, data_15_590.2]

/-- Complete interval computation for depth 15, residue 591. -/
theorem bounds_15_591 : exactInterval 15 591 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_591 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 591) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_591 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_591 : oddCount 591 15 = 8 ∧ acceleratedOrbit 15 591 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_591 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 591) = 3 ^ 8 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_591.1, data_15_591.2]

/-- Complete interval computation for depth 15, residue 592. -/
theorem bounds_15_592 : exactInterval 15 592 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_592 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 592) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_592 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_592 : oddCount 592 15 = 5 ∧ acceleratedOrbit 15 592 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_592 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 592) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_592.1, data_15_592.2]

/-- Complete interval computation for depth 15, residue 593. -/
theorem bounds_15_593 : exactInterval 15 593 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_593 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 593) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_593 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_593 : oddCount 593 15 = 10 ∧ acceleratedOrbit 15 593 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_593 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 593) = 3 ^ 10 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_593.1, data_15_593.2]

/-- Complete interval computation for depth 15, residue 594. -/
theorem bounds_15_594 : exactInterval 15 594 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_594 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 594) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_594 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_594 : oddCount 594 15 = 10 ∧ acceleratedOrbit 15 594 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_594 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 594) = 3 ^ 10 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_594.1, data_15_594.2]

/-- Complete interval computation for depth 15, residue 595. -/
theorem bounds_15_595 : exactInterval 15 595 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_595 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 595) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_595 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_595 : oddCount 595 15 = 10 ∧ acceleratedOrbit 15 595 = 1079 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_595 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 595) = 3 ^ 10 * m + 1079 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_595.1, data_15_595.2]

/-- Complete interval computation for depth 15, residue 596. -/
theorem bounds_15_596 : exactInterval 15 596 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_596 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 596) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_596 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_596 : oddCount 596 15 = 5 ∧ acceleratedOrbit 15 596 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_596 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 596) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_596.1, data_15_596.2]

/-- Complete interval computation for depth 15, residue 597. -/
theorem bounds_15_597 : exactInterval 15 597 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_597 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 597) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_597 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_597 : oddCount 597 15 = 5 ∧ acceleratedOrbit 15 597 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_597 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 597) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_597.1, data_15_597.2]

/-- Complete interval computation for depth 15, residue 598. -/
theorem bounds_15_598 : exactInterval 15 598 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_598 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 598) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_598 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_598 : oddCount 598 15 = 9 ∧ acceleratedOrbit 15 598 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_598 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 598) = 3 ^ 9 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_598.1, data_15_598.2]

/-- Complete interval computation for depth 15, residue 599. -/
theorem bounds_15_599 : exactInterval 15 599 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_599 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 599) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_599 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_599 : oddCount 599 15 = 9 ∧ acceleratedOrbit 15 599 = 364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_599 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 599) = 3 ^ 9 * m + 364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_599.1, data_15_599.2]

/-- Complete interval computation for depth 15, residue 600. -/
theorem bounds_15_600 : exactInterval 15 600 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_600 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 600) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_600 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_600 : oddCount 600 15 = 4 ∧ acceleratedOrbit 15 600 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_600 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 600) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_600.1, data_15_600.2]

/-- Complete interval computation for depth 15, residue 601. -/
theorem bounds_15_601 : exactInterval 15 601 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_601 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 601) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_601 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_601 : oddCount 601 15 = 10 ∧ acceleratedOrbit 15 601 = 1093 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_601 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 601) = 3 ^ 10 * m + 1093 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_601.1, data_15_601.2]

/-- Complete interval computation for depth 15, residue 602. -/
theorem bounds_15_602 : exactInterval 15 602 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_602 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 602) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_602 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_602 : oddCount 602 15 = 4 ∧ acceleratedOrbit 15 602 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_602 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 602) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_602.1, data_15_602.2]

/-- Complete interval computation for depth 15, residue 603. -/
theorem bounds_15_603 : exactInterval 15 603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_603 : oddCount 603 15 = 10 ∧ acceleratedOrbit 15 603 = 1090 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 603) = 3 ^ 10 * m + 1090 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_603.1, data_15_603.2]

/-- Complete interval computation for depth 15, residue 604. -/
theorem bounds_15_604 : exactInterval 15 604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_604 : oddCount 604 15 = 4 ∧ acceleratedOrbit 15 604 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 604) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_604.1, data_15_604.2]

/-- Complete interval computation for depth 15, residue 605. -/
theorem bounds_15_605 : exactInterval 15 605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_605 : oddCount 605 15 = 4 ∧ acceleratedOrbit 15 605 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 605) = 3 ^ 4 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_605.1, data_15_605.2]

/-- Complete interval computation for depth 15, residue 606. -/
theorem bounds_15_606 : exactInterval 15 606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_606 : oddCount 606 15 = 8 ∧ acceleratedOrbit 15 606 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 606) = 3 ^ 8 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_606.1, data_15_606.2]

/-- Complete interval computation for depth 15, residue 607. -/
theorem bounds_15_607 : exactInterval 15 607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_607 : oddCount 607 15 = 8 ∧ acceleratedOrbit 15 607 = 122 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 607) = 3 ^ 8 * m + 122 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_607.1, data_15_607.2]

/-- Complete interval computation for depth 15, residue 608. -/
theorem bounds_15_608 : exactInterval 15 608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_608 : oddCount 608 15 = 5 ∧ acceleratedOrbit 15 608 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 608) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_608.1, data_15_608.2]

/-- Complete interval computation for depth 15, residue 609. -/
theorem bounds_15_609 : exactInterval 15 609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_609 : oddCount 609 15 = 7 ∧ acceleratedOrbit 15 609 = 41 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 609) = 3 ^ 7 * m + 41 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_609.1, data_15_609.2]

/-- Complete interval computation for depth 15, residue 610. -/
theorem bounds_15_610 : exactInterval 15 610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_610 : oddCount 610 15 = 6 ∧ acceleratedOrbit 15 610 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 610) = 3 ^ 6 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_610.1, data_15_610.2]

/-- Complete interval computation for depth 15, residue 611. -/
theorem bounds_15_611 : exactInterval 15 611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_611 : oddCount 611 15 = 6 ∧ acceleratedOrbit 15 611 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 611) = 3 ^ 6 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_611.1, data_15_611.2]

/-- Complete interval computation for depth 15, residue 612. -/
theorem bounds_15_612 : exactInterval 15 612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_612 : oddCount 612 15 = 6 ∧ acceleratedOrbit 15 612 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 612) = 3 ^ 6 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_612.1, data_15_612.2]

/-- Complete interval computation for depth 15, residue 613. -/
theorem bounds_15_613 : exactInterval 15 613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_613 : oddCount 613 15 = 6 ∧ acceleratedOrbit 15 613 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 613) = 3 ^ 6 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_613.1, data_15_613.2]

/-- Complete interval computation for depth 15, residue 614. -/
theorem bounds_15_614 : exactInterval 15 614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_614 : oddCount 614 15 = 6 ∧ acceleratedOrbit 15 614 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 614) = 3 ^ 6 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_614.1, data_15_614.2]

/-- Complete interval computation for depth 15, residue 615. -/
theorem bounds_15_615 : exactInterval 15 615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_615 : oddCount 615 15 = 9 ∧ acceleratedOrbit 15 615 = 371 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 615) = 3 ^ 9 * m + 371 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_615.1, data_15_615.2]

/-- Complete interval computation for depth 15, residue 616. -/
theorem bounds_15_616 : exactInterval 15 616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_616 : oddCount 616 15 = 5 ∧ acceleratedOrbit 15 616 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 616) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_616.1, data_15_616.2]

/-- Complete interval computation for depth 15, residue 617. -/
theorem bounds_15_617 : exactInterval 15 617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_617 : oddCount 617 15 = 8 ∧ acceleratedOrbit 15 617 = 124 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 617) = 3 ^ 8 * m + 124 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_617.1, data_15_617.2]

/-- Complete interval computation for depth 15, residue 618. -/
theorem bounds_15_618 : exactInterval 15 618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_618 : oddCount 618 15 = 5 ∧ acceleratedOrbit 15 618 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 618) = 3 ^ 5 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_618.1, data_15_618.2]

/-- Complete interval computation for depth 15, residue 619. -/
theorem bounds_15_619 : exactInterval 15 619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_619 : oddCount 619 15 = 8 ∧ acceleratedOrbit 15 619 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 619) = 3 ^ 8 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_619.1, data_15_619.2]

/-- Complete interval computation for depth 15, residue 620. -/
theorem bounds_15_620 : exactInterval 15 620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_620 : oddCount 620 15 = 9 ∧ acceleratedOrbit 15 620 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 620) = 3 ^ 9 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_620.1, data_15_620.2]

/-- Complete interval computation for depth 15, residue 621. -/
theorem bounds_15_621 : exactInterval 15 621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_621 : oddCount 621 15 = 9 ∧ acceleratedOrbit 15 621 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 621) = 3 ^ 9 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_621.1, data_15_621.2]

end Collatz.Research.PassageAtlas.Batch0019
