import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0172

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5603. -/
theorem bounds_15_5603 : exactInterval 15 5603 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5603 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5603) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5603 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5603 : oddCount 5603 15 = 4 ∧ acceleratedOrbit 15 5603 = 14 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5603 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5603) = 3 ^ 4 * m + 14 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5603.1, data_15_5603.2]

/-- Complete interval computation for depth 15, residue 5604. -/
theorem bounds_15_5604 : exactInterval 15 5604 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5604 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5604) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5604 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5604 : oddCount 5604 15 = 10 ∧ acceleratedOrbit 15 5604 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5604 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5604) = 3 ^ 10 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5604.1, data_15_5604.2]

/-- Complete interval computation for depth 15, residue 5605. -/
theorem bounds_15_5605 : exactInterval 15 5605 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5605 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5605) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5605 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5605 : oddCount 5605 15 = 10 ∧ acceleratedOrbit 15 5605 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5605 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5605) = 3 ^ 10 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5605.1, data_15_5605.2]

/-- Complete interval computation for depth 15, residue 5606. -/
theorem bounds_15_5606 : exactInterval 15 5606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5606 : oddCount 5606 15 = 10 ∧ acceleratedOrbit 15 5606 = 10115 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5606) = 3 ^ 10 * m + 10115 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5606.1, data_15_5606.2]

/-- Complete interval computation for depth 15, residue 5607. -/
theorem bounds_15_5607 : exactInterval 15 5607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5607 : oddCount 5607 15 = 8 ∧ acceleratedOrbit 15 5607 = 1123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5607) = 3 ^ 8 * m + 1123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5607.1, data_15_5607.2]

/-- Complete interval computation for depth 15, residue 5608. -/
theorem bounds_15_5608 : exactInterval 15 5608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5608 : oddCount 5608 15 = 7 ∧ acceleratedOrbit 15 5608 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5608) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5608.1, data_15_5608.2]

/-- Complete interval computation for depth 15, residue 5609. -/
theorem bounds_15_5609 : exactInterval 15 5609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5609 : oddCount 5609 15 = 11 ∧ acceleratedOrbit 15 5609 = 30334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5609) = 3 ^ 11 * m + 30334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5609.1, data_15_5609.2]

/-- Complete interval computation for depth 15, residue 5610. -/
theorem bounds_15_5610 : exactInterval 15 5610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5610 : oddCount 5610 15 = 7 ∧ acceleratedOrbit 15 5610 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5610) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5610.1, data_15_5610.2]

/-- Complete interval computation for depth 15, residue 5611. -/
theorem bounds_15_5611 : exactInterval 15 5611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5611 : oddCount 5611 15 = 12 ∧ acceleratedOrbit 15 5611 = 91034 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5611) = 3 ^ 12 * m + 91034 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5611.1, data_15_5611.2]

/-- Complete interval computation for depth 15, residue 5612. -/
theorem bounds_15_5612 : exactInterval 15 5612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5612 : oddCount 5612 15 = 6 ∧ acceleratedOrbit 15 5612 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5612) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5612.1, data_15_5612.2]

/-- Complete interval computation for depth 15, residue 5613. -/
theorem bounds_15_5613 : exactInterval 15 5613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5613 : oddCount 5613 15 = 6 ∧ acceleratedOrbit 15 5613 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5613) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5613.1, data_15_5613.2]

/-- Complete interval computation for depth 15, residue 5614. -/
theorem bounds_15_5614 : exactInterval 15 5614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5614 : oddCount 5614 15 = 6 ∧ acceleratedOrbit 15 5614 = 125 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5614) = 3 ^ 6 * m + 125 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5614.1, data_15_5614.2]

/-- Complete interval computation for depth 15, residue 5615. -/
theorem bounds_15_5615 : exactInterval 15 5615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5615 : oddCount 5615 15 = 9 ∧ acceleratedOrbit 15 5615 = 3374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5615) = 3 ^ 9 * m + 3374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5615.1, data_15_5615.2]

/-- Complete interval computation for depth 15, residue 5616. -/
theorem bounds_15_5616 : exactInterval 15 5616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5616 : oddCount 5616 15 = 7 ∧ acceleratedOrbit 15 5616 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5616) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5616.1, data_15_5616.2]

/-- Complete interval computation for depth 15, residue 5617. -/
theorem bounds_15_5617 : exactInterval 15 5617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5617 : oddCount 5617 15 = 7 ∧ acceleratedOrbit 15 5617 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5617) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5617.1, data_15_5617.2]

/-- Complete interval computation for depth 15, residue 5618. -/
theorem bounds_15_5618 : exactInterval 15 5618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5618 : oddCount 5618 15 = 8 ∧ acceleratedOrbit 15 5618 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5618) = 3 ^ 8 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5618.1, data_15_5618.2]

/-- Complete interval computation for depth 15, residue 5619. -/
theorem bounds_15_5619 : exactInterval 15 5619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5619 : oddCount 5619 15 = 8 ∧ acceleratedOrbit 15 5619 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5619) = 3 ^ 8 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5619.1, data_15_5619.2]

/-- Complete interval computation for depth 15, residue 5620. -/
theorem bounds_15_5620 : exactInterval 15 5620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5620 : oddCount 5620 15 = 7 ∧ acceleratedOrbit 15 5620 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5620) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5620.1, data_15_5620.2]

/-- Complete interval computation for depth 15, residue 5621. -/
theorem bounds_15_5621 : exactInterval 15 5621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5621 : oddCount 5621 15 = 7 ∧ acceleratedOrbit 15 5621 = 377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5621) = 3 ^ 7 * m + 377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5621.1, data_15_5621.2]

/-- Complete interval computation for depth 15, residue 5622. -/
theorem bounds_15_5622 : exactInterval 15 5622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5622 : oddCount 5622 15 = 10 ∧ acceleratedOrbit 15 5622 = 10138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5622) = 3 ^ 10 * m + 10138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5622.1, data_15_5622.2]

/-- Complete interval computation for depth 15, residue 5623. -/
theorem bounds_15_5623 : exactInterval 15 5623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5623 : oddCount 5623 15 = 10 ∧ acceleratedOrbit 15 5623 = 10138 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5623) = 3 ^ 10 * m + 10138 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5623.1, data_15_5623.2]

/-- Complete interval computation for depth 15, residue 5624. -/
theorem bounds_15_5624 : exactInterval 15 5624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5624 : oddCount 5624 15 = 10 ∧ acceleratedOrbit 15 5624 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5624) = 3 ^ 10 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5624.1, data_15_5624.2]

/-- Complete interval computation for depth 15, residue 5625. -/
theorem bounds_15_5625 : exactInterval 15 5625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5625 : oddCount 5625 15 = 8 ∧ acceleratedOrbit 15 5625 = 1127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5625) = 3 ^ 8 * m + 1127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5625.1, data_15_5625.2]

/-- Complete interval computation for depth 15, residue 5626. -/
theorem bounds_15_5626 : exactInterval 15 5626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5626 : oddCount 5626 15 = 10 ∧ acceleratedOrbit 15 5626 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5626) = 3 ^ 10 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5626.1, data_15_5626.2]

/-- Complete interval computation for depth 15, residue 5627. -/
theorem bounds_15_5627 : exactInterval 15 5627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5627 : oddCount 5627 15 = 10 ∧ acceleratedOrbit 15 5627 = 10145 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5627) = 3 ^ 10 * m + 10145 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5627.1, data_15_5627.2]

/-- Complete interval computation for depth 15, residue 5628. -/
theorem bounds_15_5628 : exactInterval 15 5628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5628 : oddCount 5628 15 = 10 ∧ acceleratedOrbit 15 5628 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5628) = 3 ^ 10 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5628.1, data_15_5628.2]

/-- Complete interval computation for depth 15, residue 5629. -/
theorem bounds_15_5629 : exactInterval 15 5629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5629 : oddCount 5629 15 = 10 ∧ acceleratedOrbit 15 5629 = 10151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5629) = 3 ^ 10 * m + 10151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5629.1, data_15_5629.2]

/-- Complete interval computation for depth 15, residue 5630. -/
theorem bounds_15_5630 : exactInterval 15 5630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5630 : oddCount 5630 15 = 9 ∧ acceleratedOrbit 15 5630 = 3383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5630) = 3 ^ 9 * m + 3383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5630.1, data_15_5630.2]

/-- Complete interval computation for depth 15, residue 5631. -/
theorem bounds_15_5631 : exactInterval 15 5631 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5631) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5631 : oddCount 5631 15 = 9 ∧ acceleratedOrbit 15 5631 = 3383 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5631) = 3 ^ 9 * m + 3383 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5631.1, data_15_5631.2]

/-- Complete interval computation for depth 15, residue 5632. -/
theorem bounds_15_5632 : exactInterval 15 5632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5632 : oddCount 5632 15 = 3 ∧ acceleratedOrbit 15 5632 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5632) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5632.1, data_15_5632.2]

/-- Complete interval computation for depth 15, residue 5633. -/
theorem bounds_15_5633 : exactInterval 15 5633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5633 : oddCount 5633 15 = 8 ∧ acceleratedOrbit 15 5633 = 1129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5633) = 3 ^ 8 * m + 1129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5633.1, data_15_5633.2]

/-- Complete interval computation for depth 15, residue 5634. -/
theorem bounds_15_5634 : exactInterval 15 5634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5634 : oddCount 5634 15 = 8 ∧ acceleratedOrbit 15 5634 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5634) = 3 ^ 8 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5634.1, data_15_5634.2]

/-- Complete interval computation for depth 15, residue 5635. -/
theorem bounds_15_5635 : exactInterval 15 5635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5635 : oddCount 5635 15 = 8 ∧ acceleratedOrbit 15 5635 = 1133 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5635) = 3 ^ 8 * m + 1133 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5635.1, data_15_5635.2]

end Collatz.Research.PassageAtlas.Batch0172
