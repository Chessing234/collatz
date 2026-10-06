import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0574

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 18776. -/
theorem bounds_15_18776 : exactInterval 15 18776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18776 : oddCount 18776 15 = 7 ∧ acceleratedOrbit 15 18776 = 1255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18776) = 3 ^ 7 * m + 1255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18776.1, data_15_18776.2]

/-- Complete interval computation for depth 15, residue 18777. -/
theorem bounds_15_18777 : exactInterval 15 18777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18777 : oddCount 18777 15 = 9 ∧ acceleratedOrbit 15 18777 = 11285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18777) = 3 ^ 9 * m + 11285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18777.1, data_15_18777.2]

/-- Complete interval computation for depth 15, residue 18778. -/
theorem bounds_15_18778 : exactInterval 15 18778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18778 : oddCount 18778 15 = 7 ∧ acceleratedOrbit 15 18778 = 1255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18778) = 3 ^ 7 * m + 1255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18778.1, data_15_18778.2]

/-- Complete interval computation for depth 15, residue 18779. -/
theorem bounds_15_18779 : exactInterval 15 18779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18779 : oddCount 18779 15 = 8 ∧ acceleratedOrbit 15 18779 = 3761 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18779) = 3 ^ 8 * m + 3761 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18779.1, data_15_18779.2]

/-- Complete interval computation for depth 15, residue 18780. -/
theorem bounds_15_18780 : exactInterval 15 18780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18780 : oddCount 18780 15 = 7 ∧ acceleratedOrbit 15 18780 = 1255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18780) = 3 ^ 7 * m + 1255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18780.1, data_15_18780.2]

/-- Complete interval computation for depth 15, residue 18781. -/
theorem bounds_15_18781 : exactInterval 15 18781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18781 : oddCount 18781 15 = 7 ∧ acceleratedOrbit 15 18781 = 1255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18781) = 3 ^ 7 * m + 1255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18781.1, data_15_18781.2]

/-- Complete interval computation for depth 15, residue 18782. -/
theorem bounds_15_18782 : exactInterval 15 18782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18782 : oddCount 18782 15 = 9 ∧ acceleratedOrbit 15 18782 = 11285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18782) = 3 ^ 9 * m + 11285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18782.1, data_15_18782.2]

/-- Complete interval computation for depth 15, residue 18783. -/
theorem bounds_15_18783 : exactInterval 15 18783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18783 : oddCount 18783 15 = 9 ∧ acceleratedOrbit 15 18783 = 11285 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18783) = 3 ^ 9 * m + 11285 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18783.1, data_15_18783.2]

/-- Complete interval computation for depth 15, residue 18784. -/
theorem bounds_15_18784 : exactInterval 15 18784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18784 : oddCount 18784 15 = 4 ∧ acceleratedOrbit 15 18784 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18784) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18784.1, data_15_18784.2]

/-- Complete interval computation for depth 15, residue 18785. -/
theorem bounds_15_18785 : exactInterval 15 18785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18785 : oddCount 18785 15 = 11 ∧ acceleratedOrbit 15 18785 = 101573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18785) = 3 ^ 11 * m + 101573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18785.1, data_15_18785.2]

/-- Complete interval computation for depth 15, residue 18786. -/
theorem bounds_15_18786 : exactInterval 15 18786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18786 : oddCount 18786 15 = 8 ∧ acceleratedOrbit 15 18786 = 3766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18786) = 3 ^ 8 * m + 3766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18786.1, data_15_18786.2]

/-- Complete interval computation for depth 15, residue 18787. -/
theorem bounds_15_18787 : exactInterval 15 18787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18787 : oddCount 18787 15 = 8 ∧ acceleratedOrbit 15 18787 = 3766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18787) = 3 ^ 8 * m + 3766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18787.1, data_15_18787.2]

/-- Complete interval computation for depth 15, residue 18788. -/
theorem bounds_15_18788 : exactInterval 15 18788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18788 : oddCount 18788 15 = 8 ∧ acceleratedOrbit 15 18788 = 3766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18788) = 3 ^ 8 * m + 3766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18788.1, data_15_18788.2]

/-- Complete interval computation for depth 15, residue 18789. -/
theorem bounds_15_18789 : exactInterval 15 18789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18789 : oddCount 18789 15 = 8 ∧ acceleratedOrbit 15 18789 = 3766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18789) = 3 ^ 8 * m + 3766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18789.1, data_15_18789.2]

/-- Complete interval computation for depth 15, residue 18790. -/
theorem bounds_15_18790 : exactInterval 15 18790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18790 : oddCount 18790 15 = 8 ∧ acceleratedOrbit 15 18790 = 3766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18790) = 3 ^ 8 * m + 3766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18790.1, data_15_18790.2]

/-- Complete interval computation for depth 15, residue 18791. -/
theorem bounds_15_18791 : exactInterval 15 18791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18791 : oddCount 18791 15 = 11 ∧ acceleratedOrbit 15 18791 = 101594 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18791) = 3 ^ 11 * m + 101594 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18791.1, data_15_18791.2]

/-- Complete interval computation for depth 15, residue 18792. -/
theorem bounds_15_18792 : exactInterval 15 18792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18792 : oddCount 18792 15 = 4 ∧ acceleratedOrbit 15 18792 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18792) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18792.1, data_15_18792.2]

/-- Complete interval computation for depth 15, residue 18793. -/
theorem bounds_15_18793 : exactInterval 15 18793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18793 : oddCount 18793 15 = 7 ∧ acceleratedOrbit 15 18793 = 1255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18793) = 3 ^ 7 * m + 1255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18793.1, data_15_18793.2]

/-- Complete interval computation for depth 15, residue 18794. -/
theorem bounds_15_18794 : exactInterval 15 18794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18794 : oddCount 18794 15 = 4 ∧ acceleratedOrbit 15 18794 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18794) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18794.1, data_15_18794.2]

/-- Complete interval computation for depth 15, residue 18795. -/
theorem bounds_15_18795 : exactInterval 15 18795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18795 : oddCount 18795 15 = 8 ∧ acceleratedOrbit 15 18795 = 3764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18795) = 3 ^ 8 * m + 3764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18795.1, data_15_18795.2]

/-- Complete interval computation for depth 15, residue 18796. -/
theorem bounds_15_18796 : exactInterval 15 18796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18796 : oddCount 18796 15 = 10 ∧ acceleratedOrbit 15 18796 = 33884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18796) = 3 ^ 10 * m + 33884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18796.1, data_15_18796.2]

/-- Complete interval computation for depth 15, residue 18797. -/
theorem bounds_15_18797 : exactInterval 15 18797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18797 : oddCount 18797 15 = 10 ∧ acceleratedOrbit 15 18797 = 33884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18797) = 3 ^ 10 * m + 33884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18797.1, data_15_18797.2]

/-- Complete interval computation for depth 15, residue 18798. -/
theorem bounds_15_18798 : exactInterval 15 18798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18798 : oddCount 18798 15 = 10 ∧ acceleratedOrbit 15 18798 = 33884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18798) = 3 ^ 10 * m + 33884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18798.1, data_15_18798.2]

/-- Complete interval computation for depth 15, residue 18799. -/
theorem bounds_15_18799 : exactInterval 15 18799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18799 : oddCount 18799 15 = 7 ∧ acceleratedOrbit 15 18799 = 1255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18799) = 3 ^ 7 * m + 1255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18799.1, data_15_18799.2]

/-- Complete interval computation for depth 15, residue 18800. -/
theorem bounds_15_18800 : exactInterval 15 18800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18800 : oddCount 18800 15 = 4 ∧ acceleratedOrbit 15 18800 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18800) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18800.1, data_15_18800.2]

/-- Complete interval computation for depth 15, residue 18801. -/
theorem bounds_15_18801 : exactInterval 15 18801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18801 : oddCount 18801 15 = 4 ∧ acceleratedOrbit 15 18801 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18801) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18801.1, data_15_18801.2]

/-- Complete interval computation for depth 15, residue 18802. -/
theorem bounds_15_18802 : exactInterval 15 18802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18802 : oddCount 18802 15 = 9 ∧ acceleratedOrbit 15 18802 = 11299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18802) = 3 ^ 9 * m + 11299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18802.1, data_15_18802.2]

/-- Complete interval computation for depth 15, residue 18803. -/
theorem bounds_15_18803 : exactInterval 15 18803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18803 : oddCount 18803 15 = 9 ∧ acceleratedOrbit 15 18803 = 11299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18803) = 3 ^ 9 * m + 11299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18803.1, data_15_18803.2]

/-- Complete interval computation for depth 15, residue 18804. -/
theorem bounds_15_18804 : exactInterval 15 18804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18804 : oddCount 18804 15 = 4 ∧ acceleratedOrbit 15 18804 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18804) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18804.1, data_15_18804.2]

/-- Complete interval computation for depth 15, residue 18805. -/
theorem bounds_15_18805 : exactInterval 15 18805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18805 : oddCount 18805 15 = 4 ∧ acceleratedOrbit 15 18805 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18805) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18805.1, data_15_18805.2]

/-- Complete interval computation for depth 15, residue 18806. -/
theorem bounds_15_18806 : exactInterval 15 18806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18806 : oddCount 18806 15 = 10 ∧ acceleratedOrbit 15 18806 = 33898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18806) = 3 ^ 10 * m + 33898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18806.1, data_15_18806.2]

/-- Complete interval computation for depth 15, residue 18807. -/
theorem bounds_15_18807 : exactInterval 15 18807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_18807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 18807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_18807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_18807 : oddCount 18807 15 = 10 ∧ acceleratedOrbit 15 18807 = 33898 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_18807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 18807) = 3 ^ 10 * m + 33898 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_18807.1, data_15_18807.2]

end Collatz.Research.PassageAtlas.Batch0574
