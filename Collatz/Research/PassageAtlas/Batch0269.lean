import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0269

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 8781. -/
theorem bounds_15_8781 : exactInterval 15 8781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8781 : oddCount 8781 15 = 7 ∧ acceleratedOrbit 15 8781 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8781) = 3 ^ 7 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8781.1, data_15_8781.2]

/-- Complete interval computation for depth 15, residue 8782. -/
theorem bounds_15_8782 : exactInterval 15 8782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8782 : oddCount 8782 15 = 9 ∧ acceleratedOrbit 15 8782 = 5278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8782) = 3 ^ 9 * m + 5278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8782.1, data_15_8782.2]

/-- Complete interval computation for depth 15, residue 8783. -/
theorem bounds_15_8783 : exactInterval 15 8783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8783 : oddCount 8783 15 = 9 ∧ acceleratedOrbit 15 8783 = 5278 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8783) = 3 ^ 9 * m + 5278 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8783.1, data_15_8783.2]

/-- Complete interval computation for depth 15, residue 8784. -/
theorem bounds_15_8784 : exactInterval 15 8784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8784 : oddCount 8784 15 = 7 ∧ acceleratedOrbit 15 8784 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8784) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8784.1, data_15_8784.2]

/-- Complete interval computation for depth 15, residue 8785. -/
theorem bounds_15_8785 : exactInterval 15 8785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8785 : oddCount 8785 15 = 8 ∧ acceleratedOrbit 15 8785 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8785) = 3 ^ 8 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8785.1, data_15_8785.2]

/-- Complete interval computation for depth 15, residue 8786. -/
theorem bounds_15_8786 : exactInterval 15 8786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8786 : oddCount 8786 15 = 8 ∧ acceleratedOrbit 15 8786 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8786) = 3 ^ 8 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8786.1, data_15_8786.2]

/-- Complete interval computation for depth 15, residue 8787. -/
theorem bounds_15_8787 : exactInterval 15 8787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8787 : oddCount 8787 15 = 8 ∧ acceleratedOrbit 15 8787 = 1760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8787) = 3 ^ 8 * m + 1760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8787.1, data_15_8787.2]

/-- Complete interval computation for depth 15, residue 8788. -/
theorem bounds_15_8788 : exactInterval 15 8788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8788 : oddCount 8788 15 = 7 ∧ acceleratedOrbit 15 8788 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8788) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8788.1, data_15_8788.2]

/-- Complete interval computation for depth 15, residue 8789. -/
theorem bounds_15_8789 : exactInterval 15 8789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8789 : oddCount 8789 15 = 7 ∧ acceleratedOrbit 15 8789 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8789) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8789.1, data_15_8789.2]

/-- Complete interval computation for depth 15, residue 8790. -/
theorem bounds_15_8790 : exactInterval 15 8790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8790 : oddCount 8790 15 = 9 ∧ acceleratedOrbit 15 8790 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8790) = 3 ^ 9 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8790.1, data_15_8790.2]

/-- Complete interval computation for depth 15, residue 8791. -/
theorem bounds_15_8791 : exactInterval 15 8791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8791 : oddCount 8791 15 = 9 ∧ acceleratedOrbit 15 8791 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8791) = 3 ^ 9 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8791.1, data_15_8791.2]

/-- Complete interval computation for depth 15, residue 8792. -/
theorem bounds_15_8792 : exactInterval 15 8792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8792 : oddCount 8792 15 = 4 ∧ acceleratedOrbit 15 8792 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8792) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8792.1, data_15_8792.2]

/-- Complete interval computation for depth 15, residue 8793. -/
theorem bounds_15_8793 : exactInterval 15 8793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8793 : oddCount 8793 15 = 9 ∧ acceleratedOrbit 15 8793 = 5285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8793) = 3 ^ 9 * m + 5285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8793.1, data_15_8793.2]

/-- Complete interval computation for depth 15, residue 8794. -/
theorem bounds_15_8794 : exactInterval 15 8794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8794 : oddCount 8794 15 = 4 ∧ acceleratedOrbit 15 8794 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8794) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8794.1, data_15_8794.2]

/-- Complete interval computation for depth 15, residue 8795. -/
theorem bounds_15_8795 : exactInterval 15 8795 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8795) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8795 : oddCount 8795 15 = 9 ∧ acceleratedOrbit 15 8795 = 5284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8795) = 3 ^ 9 * m + 5284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8795.1, data_15_8795.2]

/-- Complete interval computation for depth 15, residue 8796. -/
theorem bounds_15_8796 : exactInterval 15 8796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8796 : oddCount 8796 15 = 4 ∧ acceleratedOrbit 15 8796 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8796) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8796.1, data_15_8796.2]

/-- Complete interval computation for depth 15, residue 8797. -/
theorem bounds_15_8797 : exactInterval 15 8797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8797 : oddCount 8797 15 = 4 ∧ acceleratedOrbit 15 8797 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8797) = 3 ^ 4 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8797.1, data_15_8797.2]

/-- Complete interval computation for depth 15, residue 8798. -/
theorem bounds_15_8798 : exactInterval 15 8798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8798 : oddCount 8798 15 = 9 ∧ acceleratedOrbit 15 8798 = 5287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8798) = 3 ^ 9 * m + 5287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8798.1, data_15_8798.2]

/-- Complete interval computation for depth 15, residue 8799. -/
theorem bounds_15_8799 : exactInterval 15 8799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8799 : oddCount 8799 15 = 9 ∧ acceleratedOrbit 15 8799 = 5287 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8799) = 3 ^ 9 * m + 5287 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8799.1, data_15_8799.2]

/-- Complete interval computation for depth 15, residue 8800. -/
theorem bounds_15_8800 : exactInterval 15 8800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8800 : oddCount 8800 15 = 7 ∧ acceleratedOrbit 15 8800 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8800) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8800.1, data_15_8800.2]

/-- Complete interval computation for depth 15, residue 8801. -/
theorem bounds_15_8801 : exactInterval 15 8801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8801 : oddCount 8801 15 = 9 ∧ acceleratedOrbit 15 8801 = 5291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8801) = 3 ^ 9 * m + 5291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8801.1, data_15_8801.2]

/-- Complete interval computation for depth 15, residue 8802. -/
theorem bounds_15_8802 : exactInterval 15 8802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8802 : oddCount 8802 15 = 7 ∧ acceleratedOrbit 15 8802 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8802) = 3 ^ 7 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8802.1, data_15_8802.2]

/-- Complete interval computation for depth 15, residue 8803. -/
theorem bounds_15_8803 : exactInterval 15 8803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8803 : oddCount 8803 15 = 7 ∧ acceleratedOrbit 15 8803 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8803) = 3 ^ 7 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8803.1, data_15_8803.2]

/-- Complete interval computation for depth 15, residue 8804. -/
theorem bounds_15_8804 : exactInterval 15 8804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8804 : oddCount 8804 15 = 7 ∧ acceleratedOrbit 15 8804 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8804) = 3 ^ 7 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8804.1, data_15_8804.2]

/-- Complete interval computation for depth 15, residue 8805. -/
theorem bounds_15_8805 : exactInterval 15 8805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8805 : oddCount 8805 15 = 7 ∧ acceleratedOrbit 15 8805 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8805) = 3 ^ 7 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8805.1, data_15_8805.2]

/-- Complete interval computation for depth 15, residue 8806. -/
theorem bounds_15_8806 : exactInterval 15 8806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8806 : oddCount 8806 15 = 7 ∧ acceleratedOrbit 15 8806 = 589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8806) = 3 ^ 7 * m + 589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8806.1, data_15_8806.2]

/-- Complete interval computation for depth 15, residue 8807. -/
theorem bounds_15_8807 : exactInterval 15 8807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8807 : oddCount 8807 15 = 10 ∧ acceleratedOrbit 15 8807 = 15875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8807) = 3 ^ 10 * m + 15875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8807.1, data_15_8807.2]

/-- Complete interval computation for depth 15, residue 8808. -/
theorem bounds_15_8808 : exactInterval 15 8808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8808 : oddCount 8808 15 = 7 ∧ acceleratedOrbit 15 8808 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8808) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8808.1, data_15_8808.2]

/-- Complete interval computation for depth 15, residue 8809. -/
theorem bounds_15_8809 : exactInterval 15 8809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8809 : oddCount 8809 15 = 9 ∧ acceleratedOrbit 15 8809 = 5293 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8809) = 3 ^ 9 * m + 5293 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8809.1, data_15_8809.2]

/-- Complete interval computation for depth 15, residue 8810. -/
theorem bounds_15_8810 : exactInterval 15 8810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8810 : oddCount 8810 15 = 7 ∧ acceleratedOrbit 15 8810 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8810) = 3 ^ 7 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8810.1, data_15_8810.2]

/-- Complete interval computation for depth 15, residue 8811. -/
theorem bounds_15_8811 : exactInterval 15 8811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8811 : oddCount 8811 15 = 8 ∧ acceleratedOrbit 15 8811 = 1765 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8811) = 3 ^ 8 * m + 1765 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8811.1, data_15_8811.2]

/-- Complete interval computation for depth 15, residue 8812. -/
theorem bounds_15_8812 : exactInterval 15 8812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8812 : oddCount 8812 15 = 8 ∧ acceleratedOrbit 15 8812 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8812) = 3 ^ 8 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8812.1, data_15_8812.2]

/-- Complete interval computation for depth 15, residue 8813. -/
theorem bounds_15_8813 : exactInterval 15 8813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_8813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 8813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_8813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_8813 : oddCount 8813 15 = 8 ∧ acceleratedOrbit 15 8813 = 1766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_8813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 8813) = 3 ^ 8 * m + 1766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_8813.1, data_15_8813.2]

end Collatz.Research.PassageAtlas.Batch0269
