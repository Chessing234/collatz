import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0974

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7777. -/
theorem bounds_13_7777 : exactInterval 13 7777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7777 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7777) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7777 : oddCount 7777 13 = 7 ∧ acceleratedOrbit 13 7777 = 2078 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7777 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7777) = 3 ^ 7 * m + 2078 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7777.1, data_13_7777.2]

/-- Complete interval computation for depth 13, residue 7778. -/
theorem bounds_13_7778 : exactInterval 13 7778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7778 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7778) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7778 : oddCount 7778 13 = 4 ∧ acceleratedOrbit 13 7778 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7778 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7778) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7778.1, data_13_7778.2]

/-- Complete interval computation for depth 13, residue 7779. -/
theorem bounds_13_7779 : exactInterval 13 7779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7779 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7779) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7779 : oddCount 7779 13 = 4 ∧ acceleratedOrbit 13 7779 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7779 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7779) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7779.1, data_13_7779.2]

/-- Complete interval computation for depth 13, residue 7780. -/
theorem bounds_13_7780 : exactInterval 13 7780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7780 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7780) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7780 : oddCount 7780 13 = 4 ∧ acceleratedOrbit 13 7780 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7780 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7780) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7780.1, data_13_7780.2]

/-- Complete interval computation for depth 13, residue 7781. -/
theorem bounds_13_7781 : exactInterval 13 7781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7781 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7781) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7781 : oddCount 7781 13 = 4 ∧ acceleratedOrbit 13 7781 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7781 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7781) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7781.1, data_13_7781.2]

/-- Complete interval computation for depth 13, residue 7782. -/
theorem bounds_13_7782 : exactInterval 13 7782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7782 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7782) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7782 : oddCount 7782 13 = 4 ∧ acceleratedOrbit 13 7782 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7782 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7782) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7782.1, data_13_7782.2]

/-- Complete interval computation for depth 13, residue 7783. -/
theorem bounds_13_7783 : exactInterval 13 7783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7783 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7783) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7783 : oddCount 7783 13 = 9 ∧ acceleratedOrbit 13 7783 = 18704 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7783 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7783) = 3 ^ 9 * m + 18704 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7783.1, data_13_7783.2]

/-- Complete interval computation for depth 13, residue 7784. -/
theorem bounds_13_7784 : exactInterval 13 7784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7784 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7784) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7784 : oddCount 7784 13 = 5 ∧ acceleratedOrbit 13 7784 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7784 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7784) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7784.1, data_13_7784.2]

/-- Complete interval computation for depth 13, residue 7785. -/
theorem bounds_13_7785 : exactInterval 13 7785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7785 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7785) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7785 : oddCount 7785 13 = 10 ∧ acceleratedOrbit 13 7785 = 56132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7785 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7785) = 3 ^ 10 * m + 56132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7785.1, data_13_7785.2]

/-- Complete interval computation for depth 13, residue 7786. -/
theorem bounds_13_7786 : exactInterval 13 7786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7786 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7786) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7786 : oddCount 7786 13 = 5 ∧ acceleratedOrbit 13 7786 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7786 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7786) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7786.1, data_13_7786.2]

/-- Complete interval computation for depth 13, residue 7787. -/
theorem bounds_13_7787 : exactInterval 13 7787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7787 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7787) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7787 : oddCount 7787 13 = 8 ∧ acceleratedOrbit 13 7787 = 6239 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7787 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7787) = 3 ^ 8 * m + 6239 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7787.1, data_13_7787.2]

/-- Complete interval computation for depth 13, residue 7788. -/
theorem bounds_13_7788 : exactInterval 13 7788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7788 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7788) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7788 : oddCount 7788 13 = 7 ∧ acceleratedOrbit 13 7788 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7788 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7788) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7788.1, data_13_7788.2]

/-- Complete interval computation for depth 13, residue 7789. -/
theorem bounds_13_7789 : exactInterval 13 7789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7789 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7789) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7789 : oddCount 7789 13 = 7 ∧ acceleratedOrbit 13 7789 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7789 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7789) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7789.1, data_13_7789.2]

/-- Complete interval computation for depth 13, residue 7790. -/
theorem bounds_13_7790 : exactInterval 13 7790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7790 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7790) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7790 : oddCount 7790 13 = 7 ∧ acceleratedOrbit 13 7790 = 2081 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7790 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7790) = 3 ^ 7 * m + 2081 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7790.1, data_13_7790.2]

/-- Complete interval computation for depth 13, residue 7791. -/
theorem bounds_13_7791 : exactInterval 13 7791 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7791 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7791) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7791 : oddCount 7791 13 = 8 ∧ acceleratedOrbit 13 7791 = 6241 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7791 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7791) = 3 ^ 8 * m + 6241 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7791.1, data_13_7791.2]

end Collatz.Research.StoppingAtlas.Batch0974
