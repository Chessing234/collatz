import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0874

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28606. -/
theorem bounds_15_28606 : exactInterval 15 28606 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28606 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28606) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28606 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28606 : oddCount 28606 15 = 9 ∧ acceleratedOrbit 15 28606 = 17185 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28606 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28606) = 3 ^ 9 * m + 17185 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28606.1, data_15_28606.2]

/-- Complete interval computation for depth 15, residue 28607. -/
theorem bounds_15_28607 : exactInterval 15 28607 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28607 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28607) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28607 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28607 : oddCount 28607 15 = 10 ∧ acceleratedOrbit 15 28607 = 51553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28607 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28607) = 3 ^ 10 * m + 51553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28607.1, data_15_28607.2]

/-- Complete interval computation for depth 15, residue 28608. -/
theorem bounds_15_28608 : exactInterval 15 28608 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28608 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28608) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28608 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28608 : oddCount 28608 15 = 8 ∧ acceleratedOrbit 15 28608 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28608 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28608) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28608.1, data_15_28608.2]

/-- Complete interval computation for depth 15, residue 28609. -/
theorem bounds_15_28609 : exactInterval 15 28609 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28609 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28609) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28609 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28609 : oddCount 28609 15 = 7 ∧ acceleratedOrbit 15 28609 = 1910 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28609 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28609) = 3 ^ 7 * m + 1910 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28609.1, data_15_28609.2]

/-- Complete interval computation for depth 15, residue 28610. -/
theorem bounds_15_28610 : exactInterval 15 28610 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28610 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28610) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28610 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28610 : oddCount 28610 15 = 9 ∧ acceleratedOrbit 15 28610 = 17189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28610 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28610) = 3 ^ 9 * m + 17189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28610.1, data_15_28610.2]

/-- Complete interval computation for depth 15, residue 28611. -/
theorem bounds_15_28611 : exactInterval 15 28611 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28611 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28611) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28611 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28611 : oddCount 28611 15 = 9 ∧ acceleratedOrbit 15 28611 = 17189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28611 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28611) = 3 ^ 9 * m + 17189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28611.1, data_15_28611.2]

/-- Complete interval computation for depth 15, residue 28612. -/
theorem bounds_15_28612 : exactInterval 15 28612 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28612 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28612) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28612 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28612 : oddCount 28612 15 = 6 ∧ acceleratedOrbit 15 28612 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28612 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28612) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28612.1, data_15_28612.2]

/-- Complete interval computation for depth 15, residue 28613. -/
theorem bounds_15_28613 : exactInterval 15 28613 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28613 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28613) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28613 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28613 : oddCount 28613 15 = 6 ∧ acceleratedOrbit 15 28613 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28613 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28613) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28613.1, data_15_28613.2]

/-- Complete interval computation for depth 15, residue 28614. -/
theorem bounds_15_28614 : exactInterval 15 28614 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28614 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28614) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28614 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28614 : oddCount 28614 15 = 6 ∧ acceleratedOrbit 15 28614 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28614 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28614) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28614.1, data_15_28614.2]

/-- Complete interval computation for depth 15, residue 28615. -/
theorem bounds_15_28615 : exactInterval 15 28615 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28615 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28615) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28615 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28615 : oddCount 28615 15 = 11 ∧ acceleratedOrbit 15 28615 = 154709 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28615 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28615) = 3 ^ 11 * m + 154709 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28615.1, data_15_28615.2]

/-- Complete interval computation for depth 15, residue 28616. -/
theorem bounds_15_28616 : exactInterval 15 28616 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28616 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28616) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28616 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28616 : oddCount 28616 15 = 6 ∧ acceleratedOrbit 15 28616 = 637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28616 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28616) = 3 ^ 6 * m + 637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28616.1, data_15_28616.2]

/-- Complete interval computation for depth 15, residue 28617. -/
theorem bounds_15_28617 : exactInterval 15 28617 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28617 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28617) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28617 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28617 : oddCount 28617 15 = 9 ∧ acceleratedOrbit 15 28617 = 17192 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28617 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28617) = 3 ^ 9 * m + 17192 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28617.1, data_15_28617.2]

/-- Complete interval computation for depth 15, residue 28618. -/
theorem bounds_15_28618 : exactInterval 15 28618 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28618 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28618) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28618 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28618 : oddCount 28618 15 = 6 ∧ acceleratedOrbit 15 28618 = 637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28618 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28618) = 3 ^ 6 * m + 637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28618.1, data_15_28618.2]

/-- Complete interval computation for depth 15, residue 28619. -/
theorem bounds_15_28619 : exactInterval 15 28619 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28619 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28619) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28619 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28619 : oddCount 28619 15 = 6 ∧ acceleratedOrbit 15 28619 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28619 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28619) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28619.1, data_15_28619.2]

/-- Complete interval computation for depth 15, residue 28620. -/
theorem bounds_15_28620 : exactInterval 15 28620 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28620 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28620) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28620 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28620 : oddCount 28620 15 = 6 ∧ acceleratedOrbit 15 28620 = 637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28620 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28620) = 3 ^ 6 * m + 637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28620.1, data_15_28620.2]

/-- Complete interval computation for depth 15, residue 28621. -/
theorem bounds_15_28621 : exactInterval 15 28621 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28621 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28621) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28621 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28621 : oddCount 28621 15 = 6 ∧ acceleratedOrbit 15 28621 = 637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28621 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28621) = 3 ^ 6 * m + 637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28621.1, data_15_28621.2]

/-- Complete interval computation for depth 15, residue 28622. -/
theorem bounds_15_28622 : exactInterval 15 28622 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28622 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28622) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28622 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28622 : oddCount 28622 15 = 8 ∧ acceleratedOrbit 15 28622 = 5732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28622 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28622) = 3 ^ 8 * m + 5732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28622.1, data_15_28622.2]

/-- Complete interval computation for depth 15, residue 28623. -/
theorem bounds_15_28623 : exactInterval 15 28623 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28623 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28623) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28623 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28623 : oddCount 28623 15 = 8 ∧ acceleratedOrbit 15 28623 = 5732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28623 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28623) = 3 ^ 8 * m + 5732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28623.1, data_15_28623.2]

/-- Complete interval computation for depth 15, residue 28624. -/
theorem bounds_15_28624 : exactInterval 15 28624 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28624 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28624) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28624 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28624 : oddCount 28624 15 = 8 ∧ acceleratedOrbit 15 28624 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28624 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28624) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28624.1, data_15_28624.2]

/-- Complete interval computation for depth 15, residue 28625. -/
theorem bounds_15_28625 : exactInterval 15 28625 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28625 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28625) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28625 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28625 : oddCount 28625 15 = 6 ∧ acceleratedOrbit 15 28625 = 637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28625 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28625) = 3 ^ 6 * m + 637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28625.1, data_15_28625.2]

/-- Complete interval computation for depth 15, residue 28626. -/
theorem bounds_15_28626 : exactInterval 15 28626 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28626 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28626) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28626 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28626 : oddCount 28626 15 = 10 ∧ acceleratedOrbit 15 28626 = 51592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28626 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28626) = 3 ^ 10 * m + 51592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28626.1, data_15_28626.2]

/-- Complete interval computation for depth 15, residue 28627. -/
theorem bounds_15_28627 : exactInterval 15 28627 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28627 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28627) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28627 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28627 : oddCount 28627 15 = 10 ∧ acceleratedOrbit 15 28627 = 51592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28627 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28627) = 3 ^ 10 * m + 51592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28627.1, data_15_28627.2]

/-- Complete interval computation for depth 15, residue 28628. -/
theorem bounds_15_28628 : exactInterval 15 28628 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28628 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28628) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28628 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28628 : oddCount 28628 15 = 8 ∧ acceleratedOrbit 15 28628 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28628 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28628) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28628.1, data_15_28628.2]

/-- Complete interval computation for depth 15, residue 28629. -/
theorem bounds_15_28629 : exactInterval 15 28629 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28629 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28629) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28629 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28629 : oddCount 28629 15 = 8 ∧ acceleratedOrbit 15 28629 = 5741 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28629 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28629) = 3 ^ 8 * m + 5741 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28629.1, data_15_28629.2]

/-- Complete interval computation for depth 15, residue 28630. -/
theorem bounds_15_28630 : exactInterval 15 28630 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28630 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28630) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28630 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28630 : oddCount 28630 15 = 9 ∧ acceleratedOrbit 15 28630 = 17200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28630 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28630) = 3 ^ 9 * m + 17200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28630.1, data_15_28630.2]

/-- Complete interval computation for depth 15, residue 28631. -/
theorem bounds_15_28631 : exactInterval 15 28631 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28631 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28631) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28631 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28631 : oddCount 28631 15 = 9 ∧ acceleratedOrbit 15 28631 = 17200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28631 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28631) = 3 ^ 9 * m + 17200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28631.1, data_15_28631.2]

/-- Complete interval computation for depth 15, residue 28632. -/
theorem bounds_15_28632 : exactInterval 15 28632 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28632 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28632) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28632 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28632 : oddCount 28632 15 = 7 ∧ acceleratedOrbit 15 28632 = 1912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28632 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28632) = 3 ^ 7 * m + 1912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28632.1, data_15_28632.2]

/-- Complete interval computation for depth 15, residue 28633. -/
theorem bounds_15_28633 : exactInterval 15 28633 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28633 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28633) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28633 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28633 : oddCount 28633 15 = 6 ∧ acceleratedOrbit 15 28633 = 638 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28633 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28633) = 3 ^ 6 * m + 638 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28633.1, data_15_28633.2]

/-- Complete interval computation for depth 15, residue 28634. -/
theorem bounds_15_28634 : exactInterval 15 28634 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28634 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28634) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28634 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28634 : oddCount 28634 15 = 7 ∧ acceleratedOrbit 15 28634 = 1912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28634 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28634) = 3 ^ 7 * m + 1912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28634.1, data_15_28634.2]

/-- Complete interval computation for depth 15, residue 28635. -/
theorem bounds_15_28635 : exactInterval 15 28635 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28635 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28635) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28635 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28635 : oddCount 28635 15 = 8 ∧ acceleratedOrbit 15 28635 = 5734 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28635 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28635) = 3 ^ 8 * m + 5734 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28635.1, data_15_28635.2]

/-- Complete interval computation for depth 15, residue 28636. -/
theorem bounds_15_28636 : exactInterval 15 28636 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28636 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28636) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28636 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28636 : oddCount 28636 15 = 7 ∧ acceleratedOrbit 15 28636 = 1912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28636 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28636) = 3 ^ 7 * m + 1912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28636.1, data_15_28636.2]

/-- Complete interval computation for depth 15, residue 28637. -/
theorem bounds_15_28637 : exactInterval 15 28637 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28637 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28637) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28637 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28637 : oddCount 28637 15 = 7 ∧ acceleratedOrbit 15 28637 = 1912 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28637 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28637) = 3 ^ 7 * m + 1912 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28637.1, data_15_28637.2]

/-- Complete interval computation for depth 15, residue 28638. -/
theorem bounds_15_28638 : exactInterval 15 28638 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28638 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28638) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28638 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28638 : oddCount 28638 15 = 8 ∧ acceleratedOrbit 15 28638 = 5735 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28638 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28638) = 3 ^ 8 * m + 5735 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28638.1, data_15_28638.2]

end Collatz.Research.PassageAtlas.Batch0874
