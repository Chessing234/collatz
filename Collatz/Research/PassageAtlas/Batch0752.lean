import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0752

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24608. -/
theorem bounds_15_24608 : exactInterval 15 24608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24608 : oddCount 24608 15 = 4 ∧ acceleratedOrbit 15 24608 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24608) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24608.1, data_15_24608.2]

/-- Complete interval computation for depth 15, residue 24609. -/
theorem bounds_15_24609 : exactInterval 15 24609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24609 : oddCount 24609 15 = 9 ∧ acceleratedOrbit 15 24609 = 14786 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24609) = 3 ^ 9 * m + 14786 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24609.1, data_15_24609.2]

/-- Complete interval computation for depth 15, residue 24610. -/
theorem bounds_15_24610 : exactInterval 15 24610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24610 : oddCount 24610 15 = 7 ∧ acceleratedOrbit 15 24610 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24610) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24610.1, data_15_24610.2]

/-- Complete interval computation for depth 15, residue 24611. -/
theorem bounds_15_24611 : exactInterval 15 24611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24611 : oddCount 24611 15 = 7 ∧ acceleratedOrbit 15 24611 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24611) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24611.1, data_15_24611.2]

/-- Complete interval computation for depth 15, residue 24612. -/
theorem bounds_15_24612 : exactInterval 15 24612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24612 : oddCount 24612 15 = 8 ∧ acceleratedOrbit 15 24612 = 4931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24612) = 3 ^ 8 * m + 4931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24612.1, data_15_24612.2]

/-- Complete interval computation for depth 15, residue 24613. -/
theorem bounds_15_24613 : exactInterval 15 24613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24613 : oddCount 24613 15 = 8 ∧ acceleratedOrbit 15 24613 = 4931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24613) = 3 ^ 8 * m + 4931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24613.1, data_15_24613.2]

/-- Complete interval computation for depth 15, residue 24614. -/
theorem bounds_15_24614 : exactInterval 15 24614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24614 : oddCount 24614 15 = 8 ∧ acceleratedOrbit 15 24614 = 4931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24614) = 3 ^ 8 * m + 4931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24614.1, data_15_24614.2]

/-- Complete interval computation for depth 15, residue 24615. -/
theorem bounds_15_24615 : exactInterval 15 24615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24615 : oddCount 24615 15 = 7 ∧ acceleratedOrbit 15 24615 = 1643 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24615) = 3 ^ 7 * m + 1643 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24615.1, data_15_24615.2]

/-- Complete interval computation for depth 15, residue 24616. -/
theorem bounds_15_24616 : exactInterval 15 24616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24616 : oddCount 24616 15 = 4 ∧ acceleratedOrbit 15 24616 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24616) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24616.1, data_15_24616.2]

/-- Complete interval computation for depth 15, residue 24617. -/
theorem bounds_15_24617 : exactInterval 15 24617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24617 : oddCount 24617 15 = 9 ∧ acceleratedOrbit 15 24617 = 14788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24617) = 3 ^ 9 * m + 14788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24617.1, data_15_24617.2]

/-- Complete interval computation for depth 15, residue 24618. -/
theorem bounds_15_24618 : exactInterval 15 24618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24618 : oddCount 24618 15 = 4 ∧ acceleratedOrbit 15 24618 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24618) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24618.1, data_15_24618.2]

/-- Complete interval computation for depth 15, residue 24619. -/
theorem bounds_15_24619 : exactInterval 15 24619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24619 : oddCount 24619 15 = 8 ∧ acceleratedOrbit 15 24619 = 4931 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24619) = 3 ^ 8 * m + 4931 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24619.1, data_15_24619.2]

/-- Complete interval computation for depth 15, residue 24620. -/
theorem bounds_15_24620 : exactInterval 15 24620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24620 : oddCount 24620 15 = 7 ∧ acceleratedOrbit 15 24620 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24620) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24620.1, data_15_24620.2]

/-- Complete interval computation for depth 15, residue 24621. -/
theorem bounds_15_24621 : exactInterval 15 24621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24621 : oddCount 24621 15 = 7 ∧ acceleratedOrbit 15 24621 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24621) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24621.1, data_15_24621.2]

/-- Complete interval computation for depth 15, residue 24622. -/
theorem bounds_15_24622 : exactInterval 15 24622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24622 : oddCount 24622 15 = 7 ∧ acceleratedOrbit 15 24622 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24622) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24622.1, data_15_24622.2]

/-- Complete interval computation for depth 15, residue 24623. -/
theorem bounds_15_24623 : exactInterval 15 24623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24623 : oddCount 24623 15 = 11 ∧ acceleratedOrbit 15 24623 = 133123 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24623) = 3 ^ 11 * m + 133123 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24623.1, data_15_24623.2]

/-- Complete interval computation for depth 15, residue 24624. -/
theorem bounds_15_24624 : exactInterval 15 24624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24624 : oddCount 24624 15 = 4 ∧ acceleratedOrbit 15 24624 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24624) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24624.1, data_15_24624.2]

/-- Complete interval computation for depth 15, residue 24625. -/
theorem bounds_15_24625 : exactInterval 15 24625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24625 : oddCount 24625 15 = 6 ∧ acceleratedOrbit 15 24625 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24625) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24625.1, data_15_24625.2]

/-- Complete interval computation for depth 15, residue 24626. -/
theorem bounds_15_24626 : exactInterval 15 24626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24626 : oddCount 24626 15 = 6 ∧ acceleratedOrbit 15 24626 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24626) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24626.1, data_15_24626.2]

/-- Complete interval computation for depth 15, residue 24627. -/
theorem bounds_15_24627 : exactInterval 15 24627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24627 : oddCount 24627 15 = 6 ∧ acceleratedOrbit 15 24627 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24627) = 3 ^ 6 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24627.1, data_15_24627.2]

/-- Complete interval computation for depth 15, residue 24628. -/
theorem bounds_15_24628 : exactInterval 15 24628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24628 : oddCount 24628 15 = 4 ∧ acceleratedOrbit 15 24628 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24628) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24628.1, data_15_24628.2]

/-- Complete interval computation for depth 15, residue 24629. -/
theorem bounds_15_24629 : exactInterval 15 24629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24629 : oddCount 24629 15 = 4 ∧ acceleratedOrbit 15 24629 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24629) = 3 ^ 4 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24629.1, data_15_24629.2]

/-- Complete interval computation for depth 15, residue 24630. -/
theorem bounds_15_24630 : exactInterval 15 24630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24630 : oddCount 24630 15 = 10 ∧ acceleratedOrbit 15 24630 = 44390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24630) = 3 ^ 10 * m + 44390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24630.1, data_15_24630.2]

/-- Complete interval computation for depth 15, residue 24631. -/
theorem bounds_15_24631 : exactInterval 15 24631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24631 : oddCount 24631 15 = 10 ∧ acceleratedOrbit 15 24631 = 44390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24631) = 3 ^ 10 * m + 44390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24631.1, data_15_24631.2]

/-- Complete interval computation for depth 15, residue 24632. -/
theorem bounds_15_24632 : exactInterval 15 24632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24632 : oddCount 24632 15 = 7 ∧ acceleratedOrbit 15 24632 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24632) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24632.1, data_15_24632.2]

/-- Complete interval computation for depth 15, residue 24633. -/
theorem bounds_15_24633 : exactInterval 15 24633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24633 : oddCount 24633 15 = 8 ∧ acceleratedOrbit 15 24633 = 4934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24633) = 3 ^ 8 * m + 4934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24633.1, data_15_24633.2]

/-- Complete interval computation for depth 15, residue 24634. -/
theorem bounds_15_24634 : exactInterval 15 24634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24634 : oddCount 24634 15 = 7 ∧ acceleratedOrbit 15 24634 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24634) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24634.1, data_15_24634.2]

/-- Complete interval computation for depth 15, residue 24635. -/
theorem bounds_15_24635 : exactInterval 15 24635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24635 : oddCount 24635 15 = 8 ∧ acceleratedOrbit 15 24635 = 4934 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24635) = 3 ^ 8 * m + 4934 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24635.1, data_15_24635.2]

/-- Complete interval computation for depth 15, residue 24636. -/
theorem bounds_15_24636 : exactInterval 15 24636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24636 : oddCount 24636 15 = 7 ∧ acceleratedOrbit 15 24636 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24636) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24636.1, data_15_24636.2]

/-- Complete interval computation for depth 15, residue 24637. -/
theorem bounds_15_24637 : exactInterval 15 24637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24637 : oddCount 24637 15 = 7 ∧ acceleratedOrbit 15 24637 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24637) = 3 ^ 7 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24637.1, data_15_24637.2]

/-- Complete interval computation for depth 15, residue 24638. -/
theorem bounds_15_24638 : exactInterval 15 24638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24638 : oddCount 24638 15 = 9 ∧ acceleratedOrbit 15 24638 = 14801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24638) = 3 ^ 9 * m + 14801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24638.1, data_15_24638.2]

/-- Complete interval computation for depth 15, residue 24639. -/
theorem bounds_15_24639 : exactInterval 15 24639 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24639) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24639 : oddCount 24639 15 = 9 ∧ acceleratedOrbit 15 24639 = 14801 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24639) = 3 ^ 9 * m + 14801 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24639.1, data_15_24639.2]

/-- Complete interval computation for depth 15, residue 24640. -/
theorem bounds_15_24640 : exactInterval 15 24640 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24640 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24640) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24640 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24640 : oddCount 24640 15 = 5 ∧ acceleratedOrbit 15 24640 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24640 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24640) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24640.1, data_15_24640.2]

end Collatz.Research.PassageAtlas.Batch0752
