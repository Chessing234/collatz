import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0813

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26607. -/
theorem bounds_15_26607 : exactInterval 15 26607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26607 : oddCount 26607 15 = 10 ∧ acceleratedOrbit 15 26607 = 47951 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26607) = 3 ^ 10 * m + 47951 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26607.1, data_15_26607.2]

/-- Complete interval computation for depth 15, residue 26608. -/
theorem bounds_15_26608 : exactInterval 15 26608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26608 : oddCount 26608 15 = 10 ∧ acceleratedOrbit 15 26608 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26608) = 3 ^ 10 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26608.1, data_15_26608.2]

/-- Complete interval computation for depth 15, residue 26609. -/
theorem bounds_15_26609 : exactInterval 15 26609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26609 : oddCount 26609 15 = 7 ∧ acceleratedOrbit 15 26609 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26609) = 3 ^ 7 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26609.1, data_15_26609.2]

/-- Complete interval computation for depth 15, residue 26610. -/
theorem bounds_15_26610 : exactInterval 15 26610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26610 : oddCount 26610 15 = 8 ∧ acceleratedOrbit 15 26610 = 5329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26610) = 3 ^ 8 * m + 5329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26610.1, data_15_26610.2]

/-- Complete interval computation for depth 15, residue 26611. -/
theorem bounds_15_26611 : exactInterval 15 26611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26611 : oddCount 26611 15 = 8 ∧ acceleratedOrbit 15 26611 = 5329 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26611) = 3 ^ 8 * m + 5329 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26611.1, data_15_26611.2]

/-- Complete interval computation for depth 15, residue 26612. -/
theorem bounds_15_26612 : exactInterval 15 26612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26612 : oddCount 26612 15 = 10 ∧ acceleratedOrbit 15 26612 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26612) = 3 ^ 10 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26612.1, data_15_26612.2]

/-- Complete interval computation for depth 15, residue 26613. -/
theorem bounds_15_26613 : exactInterval 15 26613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26613 : oddCount 26613 15 = 10 ∧ acceleratedOrbit 15 26613 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26613) = 3 ^ 10 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26613.1, data_15_26613.2]

/-- Complete interval computation for depth 15, residue 26614. -/
theorem bounds_15_26614 : exactInterval 15 26614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26614 : oddCount 26614 15 = 8 ∧ acceleratedOrbit 15 26614 = 5330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26614) = 3 ^ 8 * m + 5330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26614.1, data_15_26614.2]

/-- Complete interval computation for depth 15, residue 26615. -/
theorem bounds_15_26615 : exactInterval 15 26615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26615 : oddCount 26615 15 = 8 ∧ acceleratedOrbit 15 26615 = 5330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26615) = 3 ^ 8 * m + 5330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26615.1, data_15_26615.2]

/-- Complete interval computation for depth 15, residue 26616. -/
theorem bounds_15_26616 : exactInterval 15 26616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26616 : oddCount 26616 15 = 10 ∧ acceleratedOrbit 15 26616 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26616) = 3 ^ 10 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26616.1, data_15_26616.2]

/-- Complete interval computation for depth 15, residue 26617. -/
theorem bounds_15_26617 : exactInterval 15 26617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26617 : oddCount 26617 15 = 8 ∧ acceleratedOrbit 15 26617 = 5330 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26617) = 3 ^ 8 * m + 5330 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26617.1, data_15_26617.2]

/-- Complete interval computation for depth 15, residue 26618. -/
theorem bounds_15_26618 : exactInterval 15 26618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26618 : oddCount 26618 15 = 10 ∧ acceleratedOrbit 15 26618 = 47978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26618) = 3 ^ 10 * m + 47978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26618.1, data_15_26618.2]

/-- Complete interval computation for depth 15, residue 26619. -/
theorem bounds_15_26619 : exactInterval 15 26619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26619 : oddCount 26619 15 = 10 ∧ acceleratedOrbit 15 26619 = 47972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26619) = 3 ^ 10 * m + 47972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26619.1, data_15_26619.2]

/-- Complete interval computation for depth 15, residue 26620. -/
theorem bounds_15_26620 : exactInterval 15 26620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26620 : oddCount 26620 15 = 11 ∧ acceleratedOrbit 15 26620 = 143932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26620) = 3 ^ 11 * m + 143932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26620.1, data_15_26620.2]

/-- Complete interval computation for depth 15, residue 26621. -/
theorem bounds_15_26621 : exactInterval 15 26621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26621 : oddCount 26621 15 = 11 ∧ acceleratedOrbit 15 26621 = 143932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26621) = 3 ^ 11 * m + 143932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26621.1, data_15_26621.2]

/-- Complete interval computation for depth 15, residue 26622. -/
theorem bounds_15_26622 : exactInterval 15 26622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26622 : oddCount 26622 15 = 11 ∧ acceleratedOrbit 15 26622 = 143932 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26622) = 3 ^ 11 * m + 143932 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26622.1, data_15_26622.2]

/-- Complete interval computation for depth 15, residue 26623. -/
theorem bounds_15_26623 : exactInterval 15 26623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26623 : oddCount 26623 15 = 14 ∧ acceleratedOrbit 15 26623 = 3886163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26623) = 3 ^ 14 * m + 3886163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26623.1, data_15_26623.2]

/-- Complete interval computation for depth 15, residue 26624. -/
theorem bounds_15_26624 : exactInterval 15 26624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26624 : oddCount 26624 15 = 2 ∧ acceleratedOrbit 15 26624 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26624) = 3 ^ 2 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26624.1, data_15_26624.2]

/-- Complete interval computation for depth 15, residue 26625. -/
theorem bounds_15_26625 : exactInterval 15 26625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26625 : oddCount 26625 15 = 9 ∧ acceleratedOrbit 15 26625 = 15997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26625) = 3 ^ 9 * m + 15997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26625.1, data_15_26625.2]

/-- Complete interval computation for depth 15, residue 26626. -/
theorem bounds_15_26626 : exactInterval 15 26626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26626 : oddCount 26626 15 = 6 ∧ acceleratedOrbit 15 26626 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26626) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26626.1, data_15_26626.2]

/-- Complete interval computation for depth 15, residue 26627. -/
theorem bounds_15_26627 : exactInterval 15 26627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26627 : oddCount 26627 15 = 6 ∧ acceleratedOrbit 15 26627 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26627) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26627.1, data_15_26627.2]

/-- Complete interval computation for depth 15, residue 26628. -/
theorem bounds_15_26628 : exactInterval 15 26628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26628 : oddCount 26628 15 = 8 ∧ acceleratedOrbit 15 26628 = 5336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26628) = 3 ^ 8 * m + 5336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26628.1, data_15_26628.2]

/-- Complete interval computation for depth 15, residue 26629. -/
theorem bounds_15_26629 : exactInterval 15 26629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26629 : oddCount 26629 15 = 8 ∧ acceleratedOrbit 15 26629 = 5336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26629) = 3 ^ 8 * m + 5336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26629.1, data_15_26629.2]

/-- Complete interval computation for depth 15, residue 26630. -/
theorem bounds_15_26630 : exactInterval 15 26630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26630 : oddCount 26630 15 = 8 ∧ acceleratedOrbit 15 26630 = 5336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26630) = 3 ^ 8 * m + 5336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26630.1, data_15_26630.2]

/-- Complete interval computation for depth 15, residue 26631. -/
theorem bounds_15_26631 : exactInterval 15 26631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26631 : oddCount 26631 15 = 6 ∧ acceleratedOrbit 15 26631 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26631) = 3 ^ 6 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26631.1, data_15_26631.2]

/-- Complete interval computation for depth 15, residue 26632. -/
theorem bounds_15_26632 : exactInterval 15 26632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26632 : oddCount 26632 15 = 7 ∧ acceleratedOrbit 15 26632 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26632) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26632.1, data_15_26632.2]

/-- Complete interval computation for depth 15, residue 26633. -/
theorem bounds_15_26633 : exactInterval 15 26633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26633 : oddCount 26633 15 = 9 ∧ acceleratedOrbit 15 26633 = 16001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26633) = 3 ^ 9 * m + 16001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26633.1, data_15_26633.2]

/-- Complete interval computation for depth 15, residue 26634. -/
theorem bounds_15_26634 : exactInterval 15 26634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26634 : oddCount 26634 15 = 7 ∧ acceleratedOrbit 15 26634 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26634) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26634.1, data_15_26634.2]

/-- Complete interval computation for depth 15, residue 26635. -/
theorem bounds_15_26635 : exactInterval 15 26635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26635 : oddCount 26635 15 = 8 ∧ acceleratedOrbit 15 26635 = 5336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26635) = 3 ^ 8 * m + 5336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26635.1, data_15_26635.2]

/-- Complete interval computation for depth 15, residue 26636. -/
theorem bounds_15_26636 : exactInterval 15 26636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26636 : oddCount 26636 15 = 7 ∧ acceleratedOrbit 15 26636 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26636) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26636.1, data_15_26636.2]

/-- Complete interval computation for depth 15, residue 26637. -/
theorem bounds_15_26637 : exactInterval 15 26637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26637 : oddCount 26637 15 = 7 ∧ acceleratedOrbit 15 26637 = 1781 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26637) = 3 ^ 7 * m + 1781 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26637.1, data_15_26637.2]

/-- Complete interval computation for depth 15, residue 26638. -/
theorem bounds_15_26638 : exactInterval 15 26638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26638 : oddCount 26638 15 = 8 ∧ acceleratedOrbit 15 26638 = 5336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26638) = 3 ^ 8 * m + 5336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26638.1, data_15_26638.2]

/-- Complete interval computation for depth 15, residue 26639. -/
theorem bounds_15_26639 : exactInterval 15 26639 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26639 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26639) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26639 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26639 : oddCount 26639 15 = 8 ∧ acceleratedOrbit 15 26639 = 5336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26639 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26639) = 3 ^ 8 * m + 5336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26639.1, data_15_26639.2]

end Collatz.Research.PassageAtlas.Batch0813
