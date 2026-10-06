import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0818

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26771. -/
theorem bounds_15_26771 : exactInterval 15 26771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26771 : oddCount 26771 15 = 7 ∧ acceleratedOrbit 15 26771 = 1787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26771) = 3 ^ 7 * m + 1787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26771.1, data_15_26771.2]

/-- Complete interval computation for depth 15, residue 26772. -/
theorem bounds_15_26772 : exactInterval 15 26772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26772 : oddCount 26772 15 = 8 ∧ acceleratedOrbit 15 26772 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26772) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26772.1, data_15_26772.2]

/-- Complete interval computation for depth 15, residue 26773. -/
theorem bounds_15_26773 : exactInterval 15 26773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26773 : oddCount 26773 15 = 8 ∧ acceleratedOrbit 15 26773 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26773) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26773.1, data_15_26773.2]

/-- Complete interval computation for depth 15, residue 26774. -/
theorem bounds_15_26774 : exactInterval 15 26774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26774 : oddCount 26774 15 = 5 ∧ acceleratedOrbit 15 26774 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26774) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26774.1, data_15_26774.2]

/-- Complete interval computation for depth 15, residue 26775. -/
theorem bounds_15_26775 : exactInterval 15 26775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26775 : oddCount 26775 15 = 5 ∧ acceleratedOrbit 15 26775 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26775) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26775.1, data_15_26775.2]

/-- Complete interval computation for depth 15, residue 26776. -/
theorem bounds_15_26776 : exactInterval 15 26776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26776 : oddCount 26776 15 = 8 ∧ acceleratedOrbit 15 26776 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26776) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26776.1, data_15_26776.2]

/-- Complete interval computation for depth 15, residue 26777. -/
theorem bounds_15_26777 : exactInterval 15 26777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26777 : oddCount 26777 15 = 8 ∧ acceleratedOrbit 15 26777 = 5363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26777) = 3 ^ 8 * m + 5363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26777.1, data_15_26777.2]

/-- Complete interval computation for depth 15, residue 26778. -/
theorem bounds_15_26778 : exactInterval 15 26778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26778 : oddCount 26778 15 = 8 ∧ acceleratedOrbit 15 26778 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26778) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26778.1, data_15_26778.2]

/-- Complete interval computation for depth 15, residue 26779. -/
theorem bounds_15_26779 : exactInterval 15 26779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26779 : oddCount 26779 15 = 9 ∧ acceleratedOrbit 15 26779 = 16087 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26779) = 3 ^ 9 * m + 16087 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26779.1, data_15_26779.2]

/-- Complete interval computation for depth 15, residue 26780. -/
theorem bounds_15_26780 : exactInterval 15 26780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26780 : oddCount 26780 15 = 6 ∧ acceleratedOrbit 15 26780 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26780) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26780.1, data_15_26780.2]

/-- Complete interval computation for depth 15, residue 26781. -/
theorem bounds_15_26781 : exactInterval 15 26781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26781 : oddCount 26781 15 = 6 ∧ acceleratedOrbit 15 26781 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26781) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26781.1, data_15_26781.2]

/-- Complete interval computation for depth 15, residue 26782. -/
theorem bounds_15_26782 : exactInterval 15 26782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26782 : oddCount 26782 15 = 6 ∧ acceleratedOrbit 15 26782 = 596 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26782) = 3 ^ 6 * m + 596 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26782.1, data_15_26782.2]

/-- Complete interval computation for depth 15, residue 26783. -/
theorem bounds_15_26783 : exactInterval 15 26783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26783 : oddCount 26783 15 = 12 ∧ acceleratedOrbit 15 26783 = 434393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26783) = 3 ^ 12 * m + 434393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26783.1, data_15_26783.2]

/-- Complete interval computation for depth 15, residue 26784. -/
theorem bounds_15_26784 : exactInterval 15 26784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26784 : oddCount 26784 15 = 4 ∧ acceleratedOrbit 15 26784 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26784) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26784.1, data_15_26784.2]

/-- Complete interval computation for depth 15, residue 26785. -/
theorem bounds_15_26785 : exactInterval 15 26785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26785 : oddCount 26785 15 = 10 ∧ acceleratedOrbit 15 26785 = 48275 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26785) = 3 ^ 10 * m + 48275 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26785.1, data_15_26785.2]

/-- Complete interval computation for depth 15, residue 26786. -/
theorem bounds_15_26786 : exactInterval 15 26786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26786 : oddCount 26786 15 = 8 ∧ acceleratedOrbit 15 26786 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26786) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26786.1, data_15_26786.2]

/-- Complete interval computation for depth 15, residue 26787. -/
theorem bounds_15_26787 : exactInterval 15 26787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26787 : oddCount 26787 15 = 8 ∧ acceleratedOrbit 15 26787 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26787) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26787.1, data_15_26787.2]

/-- Complete interval computation for depth 15, residue 26788. -/
theorem bounds_15_26788 : exactInterval 15 26788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26788 : oddCount 26788 15 = 8 ∧ acceleratedOrbit 15 26788 = 5365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26788) = 3 ^ 8 * m + 5365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26788.1, data_15_26788.2]

/-- Complete interval computation for depth 15, residue 26789. -/
theorem bounds_15_26789 : exactInterval 15 26789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26789 : oddCount 26789 15 = 8 ∧ acceleratedOrbit 15 26789 = 5365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26789) = 3 ^ 8 * m + 5365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26789.1, data_15_26789.2]

/-- Complete interval computation for depth 15, residue 26790. -/
theorem bounds_15_26790 : exactInterval 15 26790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26790 : oddCount 26790 15 = 8 ∧ acceleratedOrbit 15 26790 = 5365 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26790) = 3 ^ 8 * m + 5365 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26790.1, data_15_26790.2]

/-- Complete interval computation for depth 15, residue 26791. -/
theorem bounds_15_26791 : exactInterval 15 26791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26791 : oddCount 26791 15 = 10 ∧ acceleratedOrbit 15 26791 = 48281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26791) = 3 ^ 10 * m + 48281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26791.1, data_15_26791.2]

/-- Complete interval computation for depth 15, residue 26792. -/
theorem bounds_15_26792 : exactInterval 15 26792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26792 : oddCount 26792 15 = 4 ∧ acceleratedOrbit 15 26792 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26792) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26792.1, data_15_26792.2]

/-- Complete interval computation for depth 15, residue 26793. -/
theorem bounds_15_26793 : exactInterval 15 26793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26793 : oddCount 26793 15 = 13 ∧ acceleratedOrbit 15 26793 = 1303694 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26793) = 3 ^ 13 * m + 1303694 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26793.1, data_15_26793.2]

/-- Complete interval computation for depth 15, residue 26794. -/
theorem bounds_15_26794 : exactInterval 15 26794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26794 : oddCount 26794 15 = 4 ∧ acceleratedOrbit 15 26794 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26794) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26794.1, data_15_26794.2]

/-- Complete interval computation for depth 15, residue 26795. -/
theorem bounds_15_26795 : exactInterval 15 26795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26795 : oddCount 26795 15 = 8 ∧ acceleratedOrbit 15 26795 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26795) = 3 ^ 8 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26795.1, data_15_26795.2]

/-- Complete interval computation for depth 15, residue 26796. -/
theorem bounds_15_26796 : exactInterval 15 26796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26796 : oddCount 26796 15 = 5 ∧ acceleratedOrbit 15 26796 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26796) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26796.1, data_15_26796.2]

/-- Complete interval computation for depth 15, residue 26797. -/
theorem bounds_15_26797 : exactInterval 15 26797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26797 : oddCount 26797 15 = 5 ∧ acceleratedOrbit 15 26797 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26797) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26797.1, data_15_26797.2]

/-- Complete interval computation for depth 15, residue 26798. -/
theorem bounds_15_26798 : exactInterval 15 26798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26798 : oddCount 26798 15 = 5 ∧ acceleratedOrbit 15 26798 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26798) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26798.1, data_15_26798.2]

/-- Complete interval computation for depth 15, residue 26799. -/
theorem bounds_15_26799 : exactInterval 15 26799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26799 : oddCount 26799 15 = 10 ∧ acceleratedOrbit 15 26799 = 48296 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26799) = 3 ^ 10 * m + 48296 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26799.1, data_15_26799.2]

/-- Complete interval computation for depth 15, residue 26800. -/
theorem bounds_15_26800 : exactInterval 15 26800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26800 : oddCount 26800 15 = 5 ∧ acceleratedOrbit 15 26800 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26800) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26800.1, data_15_26800.2]

/-- Complete interval computation for depth 15, residue 26801. -/
theorem bounds_15_26801 : exactInterval 15 26801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26801 : oddCount 26801 15 = 7 ∧ acceleratedOrbit 15 26801 = 1790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26801) = 3 ^ 7 * m + 1790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26801.1, data_15_26801.2]

/-- Complete interval computation for depth 15, residue 26802. -/
theorem bounds_15_26802 : exactInterval 15 26802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26802 : oddCount 26802 15 = 7 ∧ acceleratedOrbit 15 26802 = 1790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26802) = 3 ^ 7 * m + 1790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26802.1, data_15_26802.2]

/-- Complete interval computation for depth 15, residue 26803. -/
theorem bounds_15_26803 : exactInterval 15 26803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26803 : oddCount 26803 15 = 7 ∧ acceleratedOrbit 15 26803 = 1790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26803) = 3 ^ 7 * m + 1790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26803.1, data_15_26803.2]

end Collatz.Research.PassageAtlas.Batch0818
