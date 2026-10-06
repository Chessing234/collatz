import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0754

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24674. -/
theorem bounds_15_24674 : exactInterval 15 24674 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24674 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24674) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24674 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24674 : oddCount 24674 15 = 7 ∧ acceleratedOrbit 15 24674 = 1648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24674 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24674) = 3 ^ 7 * m + 1648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24674.1, data_15_24674.2]

/-- Complete interval computation for depth 15, residue 24675. -/
theorem bounds_15_24675 : exactInterval 15 24675 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24675 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24675) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24675 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24675 : oddCount 24675 15 = 7 ∧ acceleratedOrbit 15 24675 = 1648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24675 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24675) = 3 ^ 7 * m + 1648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24675.1, data_15_24675.2]

/-- Complete interval computation for depth 15, residue 24676. -/
theorem bounds_15_24676 : exactInterval 15 24676 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24676 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24676) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24676 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24676 : oddCount 24676 15 = 7 ∧ acceleratedOrbit 15 24676 = 1648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24676 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24676) = 3 ^ 7 * m + 1648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24676.1, data_15_24676.2]

/-- Complete interval computation for depth 15, residue 24677. -/
theorem bounds_15_24677 : exactInterval 15 24677 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24677 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24677) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24677 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24677 : oddCount 24677 15 = 7 ∧ acceleratedOrbit 15 24677 = 1648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24677 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24677) = 3 ^ 7 * m + 1648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24677.1, data_15_24677.2]

/-- Complete interval computation for depth 15, residue 24678. -/
theorem bounds_15_24678 : exactInterval 15 24678 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24678 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24678) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24678 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24678 : oddCount 24678 15 = 7 ∧ acceleratedOrbit 15 24678 = 1648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24678 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24678) = 3 ^ 7 * m + 1648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24678.1, data_15_24678.2]

/-- Complete interval computation for depth 15, residue 24679. -/
theorem bounds_15_24679 : exactInterval 15 24679 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24679 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24679) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24679 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24679 : oddCount 24679 15 = 9 ∧ acceleratedOrbit 15 24679 = 14825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24679 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24679) = 3 ^ 9 * m + 14825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24679.1, data_15_24679.2]

/-- Complete interval computation for depth 15, residue 24680. -/
theorem bounds_15_24680 : exactInterval 15 24680 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24680 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24680) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24680 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24680 : oddCount 24680 15 = 5 ∧ acceleratedOrbit 15 24680 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24680 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24680) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24680.1, data_15_24680.2]

/-- Complete interval computation for depth 15, residue 24681. -/
theorem bounds_15_24681 : exactInterval 15 24681 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24681 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24681) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24681 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24681 : oddCount 24681 15 = 8 ∧ acceleratedOrbit 15 24681 = 4943 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24681 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24681) = 3 ^ 8 * m + 4943 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24681.1, data_15_24681.2]

/-- Complete interval computation for depth 15, residue 24682. -/
theorem bounds_15_24682 : exactInterval 15 24682 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24682 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24682) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24682 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24682 : oddCount 24682 15 = 5 ∧ acceleratedOrbit 15 24682 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24682 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24682) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24682.1, data_15_24682.2]

/-- Complete interval computation for depth 15, residue 24683. -/
theorem bounds_15_24683 : exactInterval 15 24683 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24683 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24683) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24683 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24683 : oddCount 24683 15 = 9 ∧ acceleratedOrbit 15 24683 = 14828 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24683 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24683) = 3 ^ 9 * m + 14828 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24683.1, data_15_24683.2]

/-- Complete interval computation for depth 15, residue 24684. -/
theorem bounds_15_24684 : exactInterval 15 24684 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24684 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24684) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24684 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24684 : oddCount 24684 15 = 9 ∧ acceleratedOrbit 15 24684 = 14831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24684 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24684) = 3 ^ 9 * m + 14831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24684.1, data_15_24684.2]

/-- Complete interval computation for depth 15, residue 24685. -/
theorem bounds_15_24685 : exactInterval 15 24685 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24685 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24685) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24685 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24685 : oddCount 24685 15 = 9 ∧ acceleratedOrbit 15 24685 = 14831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24685 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24685) = 3 ^ 9 * m + 14831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24685.1, data_15_24685.2]

/-- Complete interval computation for depth 15, residue 24686. -/
theorem bounds_15_24686 : exactInterval 15 24686 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24686 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24686) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24686 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24686 : oddCount 24686 15 = 9 ∧ acceleratedOrbit 15 24686 = 14831 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24686 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24686) = 3 ^ 9 * m + 14831 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24686.1, data_15_24686.2]

/-- Complete interval computation for depth 15, residue 24687. -/
theorem bounds_15_24687 : exactInterval 15 24687 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24687 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24687) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24687 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24687 : oddCount 24687 15 = 12 ∧ acceleratedOrbit 15 24687 = 400403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24687 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24687) = 3 ^ 12 * m + 400403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24687.1, data_15_24687.2]

/-- Complete interval computation for depth 15, residue 24688. -/
theorem bounds_15_24688 : exactInterval 15 24688 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24688 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24688) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24688 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24688 : oddCount 24688 15 = 6 ∧ acceleratedOrbit 15 24688 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24688 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24688) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24688.1, data_15_24688.2]

/-- Complete interval computation for depth 15, residue 24689. -/
theorem bounds_15_24689 : exactInterval 15 24689 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24689 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24689) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24689 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24689 : oddCount 24689 15 = 5 ∧ acceleratedOrbit 15 24689 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24689 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24689) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24689.1, data_15_24689.2]

/-- Complete interval computation for depth 15, residue 24690. -/
theorem bounds_15_24690 : exactInterval 15 24690 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24690 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24690) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24690 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24690 : oddCount 24690 15 = 7 ∧ acceleratedOrbit 15 24690 = 1649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24690 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24690) = 3 ^ 7 * m + 1649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24690.1, data_15_24690.2]

/-- Complete interval computation for depth 15, residue 24691. -/
theorem bounds_15_24691 : exactInterval 15 24691 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24691 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24691) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24691 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24691 : oddCount 24691 15 = 7 ∧ acceleratedOrbit 15 24691 = 1649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24691 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24691) = 3 ^ 7 * m + 1649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24691.1, data_15_24691.2]

/-- Complete interval computation for depth 15, residue 24692. -/
theorem bounds_15_24692 : exactInterval 15 24692 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24692 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24692) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24692 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24692 : oddCount 24692 15 = 6 ∧ acceleratedOrbit 15 24692 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24692 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24692) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24692.1, data_15_24692.2]

/-- Complete interval computation for depth 15, residue 24693. -/
theorem bounds_15_24693 : exactInterval 15 24693 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24693 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24693) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24693 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24693 : oddCount 24693 15 = 6 ∧ acceleratedOrbit 15 24693 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24693 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24693) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24693.1, data_15_24693.2]

/-- Complete interval computation for depth 15, residue 24694. -/
theorem bounds_15_24694 : exactInterval 15 24694 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24694 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24694) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24694 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24694 : oddCount 24694 15 = 7 ∧ acceleratedOrbit 15 24694 = 1649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24694 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24694) = 3 ^ 7 * m + 1649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24694.1, data_15_24694.2]

/-- Complete interval computation for depth 15, residue 24695. -/
theorem bounds_15_24695 : exactInterval 15 24695 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24695 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24695) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24695 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24695 : oddCount 24695 15 = 7 ∧ acceleratedOrbit 15 24695 = 1649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24695 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24695) = 3 ^ 7 * m + 1649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24695.1, data_15_24695.2]

/-- Complete interval computation for depth 15, residue 24696. -/
theorem bounds_15_24696 : exactInterval 15 24696 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24696 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24696) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24696 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24696 : oddCount 24696 15 = 6 ∧ acceleratedOrbit 15 24696 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24696 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24696) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24696.1, data_15_24696.2]

/-- Complete interval computation for depth 15, residue 24697. -/
theorem bounds_15_24697 : exactInterval 15 24697 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24697 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24697) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24697 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24697 : oddCount 24697 15 = 11 ∧ acceleratedOrbit 15 24697 = 133528 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24697 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24697) = 3 ^ 11 * m + 133528 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24697.1, data_15_24697.2]

/-- Complete interval computation for depth 15, residue 24698. -/
theorem bounds_15_24698 : exactInterval 15 24698 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24698 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24698) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24698 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24698 : oddCount 24698 15 = 6 ∧ acceleratedOrbit 15 24698 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24698 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24698) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24698.1, data_15_24698.2]

/-- Complete interval computation for depth 15, residue 24699. -/
theorem bounds_15_24699 : exactInterval 15 24699 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24699 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24699) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24699 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24699 : oddCount 24699 15 = 8 ∧ acceleratedOrbit 15 24699 = 4946 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24699 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24699) = 3 ^ 8 * m + 4946 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24699.1, data_15_24699.2]

/-- Complete interval computation for depth 15, residue 24700. -/
theorem bounds_15_24700 : exactInterval 15 24700 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24700 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24700) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24700 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24700 : oddCount 24700 15 = 9 ∧ acceleratedOrbit 15 24700 = 14840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24700 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24700) = 3 ^ 9 * m + 14840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24700.1, data_15_24700.2]

/-- Complete interval computation for depth 15, residue 24701. -/
theorem bounds_15_24701 : exactInterval 15 24701 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24701 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24701) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24701 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24701 : oddCount 24701 15 = 9 ∧ acceleratedOrbit 15 24701 = 14840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24701 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24701) = 3 ^ 9 * m + 14840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24701.1, data_15_24701.2]

/-- Complete interval computation for depth 15, residue 24702. -/
theorem bounds_15_24702 : exactInterval 15 24702 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24702 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24702) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24702 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24702 : oddCount 24702 15 = 9 ∧ acceleratedOrbit 15 24702 = 14840 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24702 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24702) = 3 ^ 9 * m + 14840 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24702.1, data_15_24702.2]

/-- Complete interval computation for depth 15, residue 24703. -/
theorem bounds_15_24703 : exactInterval 15 24703 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24703 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24703) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24703 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24703 : oddCount 24703 15 = 10 ∧ acceleratedOrbit 15 24703 = 44518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24703 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24703) = 3 ^ 10 * m + 44518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24703.1, data_15_24703.2]

/-- Complete interval computation for depth 15, residue 24704. -/
theorem bounds_15_24704 : exactInterval 15 24704 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24704 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24704) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24704 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24704 : oddCount 24704 15 = 4 ∧ acceleratedOrbit 15 24704 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24704 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24704) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24704.1, data_15_24704.2]

/-- Complete interval computation for depth 15, residue 24705. -/
theorem bounds_15_24705 : exactInterval 15 24705 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24705 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24705) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24705 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24705 : oddCount 24705 15 = 9 ∧ acceleratedOrbit 15 24705 = 14843 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24705 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24705) = 3 ^ 9 * m + 14843 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24705.1, data_15_24705.2]

/-- Complete interval computation for depth 15, residue 24706. -/
theorem bounds_15_24706 : exactInterval 15 24706 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24706 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24706) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24706 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24706 : oddCount 24706 15 = 6 ∧ acceleratedOrbit 15 24706 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24706 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24706) = 3 ^ 6 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24706.1, data_15_24706.2]

end Collatz.Research.PassageAtlas.Batch0754
