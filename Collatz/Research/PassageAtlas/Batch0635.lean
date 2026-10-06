import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0635

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20774. -/
theorem bounds_15_20774 : exactInterval 15 20774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20774 : oddCount 20774 15 = 7 ∧ acceleratedOrbit 15 20774 = 1387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20774) = 3 ^ 7 * m + 1387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20774.1, data_15_20774.2]

/-- Complete interval computation for depth 15, residue 20775. -/
theorem bounds_15_20775 : exactInterval 15 20775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20775 : oddCount 20775 15 = 10 ∧ acceleratedOrbit 15 20775 = 37442 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20775) = 3 ^ 10 * m + 37442 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20775.1, data_15_20775.2]

/-- Complete interval computation for depth 15, residue 20776. -/
theorem bounds_15_20776 : exactInterval 15 20776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20776 : oddCount 20776 15 = 7 ∧ acceleratedOrbit 15 20776 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20776) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20776.1, data_15_20776.2]

/-- Complete interval computation for depth 15, residue 20777. -/
theorem bounds_15_20777 : exactInterval 15 20777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20777 : oddCount 20777 15 = 9 ∧ acceleratedOrbit 15 20777 = 12482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20777) = 3 ^ 9 * m + 12482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20777.1, data_15_20777.2]

/-- Complete interval computation for depth 15, residue 20778. -/
theorem bounds_15_20778 : exactInterval 15 20778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20778 : oddCount 20778 15 = 7 ∧ acceleratedOrbit 15 20778 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20778) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20778.1, data_15_20778.2]

/-- Complete interval computation for depth 15, residue 20779. -/
theorem bounds_15_20779 : exactInterval 15 20779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20779 : oddCount 20779 15 = 9 ∧ acceleratedOrbit 15 20779 = 12484 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20779) = 3 ^ 9 * m + 12484 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20779.1, data_15_20779.2]

/-- Complete interval computation for depth 15, residue 20780. -/
theorem bounds_15_20780 : exactInterval 15 20780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20780 : oddCount 20780 15 = 5 ∧ acceleratedOrbit 15 20780 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20780) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20780.1, data_15_20780.2]

/-- Complete interval computation for depth 15, residue 20781. -/
theorem bounds_15_20781 : exactInterval 15 20781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20781 : oddCount 20781 15 = 5 ∧ acceleratedOrbit 15 20781 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20781) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20781.1, data_15_20781.2]

/-- Complete interval computation for depth 15, residue 20782. -/
theorem bounds_15_20782 : exactInterval 15 20782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20782 : oddCount 20782 15 = 5 ∧ acceleratedOrbit 15 20782 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20782) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20782.1, data_15_20782.2]

/-- Complete interval computation for depth 15, residue 20783. -/
theorem bounds_15_20783 : exactInterval 15 20783 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20783) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20783 : oddCount 20783 15 = 9 ∧ acceleratedOrbit 15 20783 = 12485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20783) = 3 ^ 9 * m + 12485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20783.1, data_15_20783.2]

/-- Complete interval computation for depth 15, residue 20784. -/
theorem bounds_15_20784 : exactInterval 15 20784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20784 : oddCount 20784 15 = 7 ∧ acceleratedOrbit 15 20784 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20784) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20784.1, data_15_20784.2]

/-- Complete interval computation for depth 15, residue 20785. -/
theorem bounds_15_20785 : exactInterval 15 20785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20785 : oddCount 20785 15 = 7 ∧ acceleratedOrbit 15 20785 = 1388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20785) = 3 ^ 7 * m + 1388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20785.1, data_15_20785.2]

/-- Complete interval computation for depth 15, residue 20786. -/
theorem bounds_15_20786 : exactInterval 15 20786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20786 : oddCount 20786 15 = 7 ∧ acceleratedOrbit 15 20786 = 1388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20786) = 3 ^ 7 * m + 1388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20786.1, data_15_20786.2]

/-- Complete interval computation for depth 15, residue 20787. -/
theorem bounds_15_20787 : exactInterval 15 20787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20787 : oddCount 20787 15 = 7 ∧ acceleratedOrbit 15 20787 = 1388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20787) = 3 ^ 7 * m + 1388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20787.1, data_15_20787.2]

/-- Complete interval computation for depth 15, residue 20788. -/
theorem bounds_15_20788 : exactInterval 15 20788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20788 : oddCount 20788 15 = 7 ∧ acceleratedOrbit 15 20788 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20788) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20788.1, data_15_20788.2]

/-- Complete interval computation for depth 15, residue 20789. -/
theorem bounds_15_20789 : exactInterval 15 20789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20789 : oddCount 20789 15 = 7 ∧ acceleratedOrbit 15 20789 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20789) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20789.1, data_15_20789.2]

/-- Complete interval computation for depth 15, residue 20790. -/
theorem bounds_15_20790 : exactInterval 15 20790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20790 : oddCount 20790 15 = 9 ∧ acceleratedOrbit 15 20790 = 12491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20790) = 3 ^ 9 * m + 12491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20790.1, data_15_20790.2]

/-- Complete interval computation for depth 15, residue 20791. -/
theorem bounds_15_20791 : exactInterval 15 20791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20791 : oddCount 20791 15 = 9 ∧ acceleratedOrbit 15 20791 = 12491 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20791) = 3 ^ 9 * m + 12491 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20791.1, data_15_20791.2]

/-- Complete interval computation for depth 15, residue 20792. -/
theorem bounds_15_20792 : exactInterval 15 20792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20792 : oddCount 20792 15 = 6 ∧ acceleratedOrbit 15 20792 = 463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20792) = 3 ^ 6 * m + 463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20792.1, data_15_20792.2]

/-- Complete interval computation for depth 15, residue 20793. -/
theorem bounds_15_20793 : exactInterval 15 20793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20793 : oddCount 20793 15 = 11 ∧ acceleratedOrbit 15 20793 = 112427 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20793) = 3 ^ 11 * m + 112427 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20793.1, data_15_20793.2]

/-- Complete interval computation for depth 15, residue 20794. -/
theorem bounds_15_20794 : exactInterval 15 20794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20794 : oddCount 20794 15 = 6 ∧ acceleratedOrbit 15 20794 = 463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20794) = 3 ^ 6 * m + 463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20794.1, data_15_20794.2]

/-- Complete interval computation for depth 15, residue 20795. -/
theorem bounds_15_20795 : exactInterval 15 20795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20795 : oddCount 20795 15 = 6 ∧ acceleratedOrbit 15 20795 = 463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20795) = 3 ^ 6 * m + 463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20795.1, data_15_20795.2]

/-- Complete interval computation for depth 15, residue 20796. -/
theorem bounds_15_20796 : exactInterval 15 20796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20796 : oddCount 20796 15 = 6 ∧ acceleratedOrbit 15 20796 = 463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20796) = 3 ^ 6 * m + 463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20796.1, data_15_20796.2]

/-- Complete interval computation for depth 15, residue 20797. -/
theorem bounds_15_20797 : exactInterval 15 20797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20797 : oddCount 20797 15 = 6 ∧ acceleratedOrbit 15 20797 = 463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20797) = 3 ^ 6 * m + 463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20797.1, data_15_20797.2]

/-- Complete interval computation for depth 15, residue 20798. -/
theorem bounds_15_20798 : exactInterval 15 20798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20798 : oddCount 20798 15 = 11 ∧ acceleratedOrbit 15 20798 = 112448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20798) = 3 ^ 11 * m + 112448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20798.1, data_15_20798.2]

/-- Complete interval computation for depth 15, residue 20799. -/
theorem bounds_15_20799 : exactInterval 15 20799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20799 : oddCount 20799 15 = 11 ∧ acceleratedOrbit 15 20799 = 112448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20799) = 3 ^ 11 * m + 112448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20799.1, data_15_20799.2]

/-- Complete interval computation for depth 15, residue 20800. -/
theorem bounds_15_20800 : exactInterval 15 20800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20800 : oddCount 20800 15 = 4 ∧ acceleratedOrbit 15 20800 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20800) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20800.1, data_15_20800.2]

/-- Complete interval computation for depth 15, residue 20801. -/
theorem bounds_15_20801 : exactInterval 15 20801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20801 : oddCount 20801 15 = 7 ∧ acceleratedOrbit 15 20801 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20801) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20801.1, data_15_20801.2]

/-- Complete interval computation for depth 15, residue 20802. -/
theorem bounds_15_20802 : exactInterval 15 20802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20802 : oddCount 20802 15 = 9 ∧ acceleratedOrbit 15 20802 = 12500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20802) = 3 ^ 9 * m + 12500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20802.1, data_15_20802.2]

/-- Complete interval computation for depth 15, residue 20803. -/
theorem bounds_15_20803 : exactInterval 15 20803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20803 : oddCount 20803 15 = 9 ∧ acceleratedOrbit 15 20803 = 12500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20803) = 3 ^ 9 * m + 12500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20803.1, data_15_20803.2]

/-- Complete interval computation for depth 15, residue 20804. -/
theorem bounds_15_20804 : exactInterval 15 20804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20804 : oddCount 20804 15 = 7 ∧ acceleratedOrbit 15 20804 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20804) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20804.1, data_15_20804.2]

/-- Complete interval computation for depth 15, residue 20805. -/
theorem bounds_15_20805 : exactInterval 15 20805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20805 : oddCount 20805 15 = 7 ∧ acceleratedOrbit 15 20805 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20805) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20805.1, data_15_20805.2]

/-- Complete interval computation for depth 15, residue 20806. -/
theorem bounds_15_20806 : exactInterval 15 20806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20806 : oddCount 20806 15 = 7 ∧ acceleratedOrbit 15 20806 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20806) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20806.1, data_15_20806.2]

end Collatz.Research.PassageAtlas.Batch0635
