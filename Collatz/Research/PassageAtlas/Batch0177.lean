import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0177

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5767. -/
theorem bounds_15_5767 : exactInterval 15 5767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5767 : oddCount 5767 15 = 8 ∧ acceleratedOrbit 15 5767 = 1156 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5767) = 3 ^ 8 * m + 1156 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5767.1, data_15_5767.2]

/-- Complete interval computation for depth 15, residue 5768. -/
theorem bounds_15_5768 : exactInterval 15 5768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5768 : oddCount 5768 15 = 5 ∧ acceleratedOrbit 15 5768 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5768) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5768.1, data_15_5768.2]

/-- Complete interval computation for depth 15, residue 5769. -/
theorem bounds_15_5769 : exactInterval 15 5769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5769 : oddCount 5769 15 = 9 ∧ acceleratedOrbit 15 5769 = 3467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5769) = 3 ^ 9 * m + 3467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5769.1, data_15_5769.2]

/-- Complete interval computation for depth 15, residue 5770. -/
theorem bounds_15_5770 : exactInterval 15 5770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5770 : oddCount 5770 15 = 5 ∧ acceleratedOrbit 15 5770 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5770) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5770.1, data_15_5770.2]

/-- Complete interval computation for depth 15, residue 5771. -/
theorem bounds_15_5771 : exactInterval 15 5771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5771 : oddCount 5771 15 = 7 ∧ acceleratedOrbit 15 5771 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5771) = 3 ^ 7 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5771.1, data_15_5771.2]

/-- Complete interval computation for depth 15, residue 5772. -/
theorem bounds_15_5772 : exactInterval 15 5772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5772 : oddCount 5772 15 = 5 ∧ acceleratedOrbit 15 5772 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5772) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5772.1, data_15_5772.2]

/-- Complete interval computation for depth 15, residue 5773. -/
theorem bounds_15_5773 : exactInterval 15 5773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5773 : oddCount 5773 15 = 5 ∧ acceleratedOrbit 15 5773 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5773) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5773.1, data_15_5773.2]

/-- Complete interval computation for depth 15, residue 5774. -/
theorem bounds_15_5774 : exactInterval 15 5774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5774 : oddCount 5774 15 = 10 ∧ acceleratedOrbit 15 5774 = 10412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5774) = 3 ^ 10 * m + 10412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5774.1, data_15_5774.2]

/-- Complete interval computation for depth 15, residue 5775. -/
theorem bounds_15_5775 : exactInterval 15 5775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5775 : oddCount 5775 15 = 10 ∧ acceleratedOrbit 15 5775 = 10412 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5775) = 3 ^ 10 * m + 10412 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5775.1, data_15_5775.2]

/-- Complete interval computation for depth 15, residue 5776. -/
theorem bounds_15_5776 : exactInterval 15 5776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5776 : oddCount 5776 15 = 5 ∧ acceleratedOrbit 15 5776 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5776) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5776.1, data_15_5776.2]

/-- Complete interval computation for depth 15, residue 5777. -/
theorem bounds_15_5777 : exactInterval 15 5777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5777 : oddCount 5777 15 = 8 ∧ acceleratedOrbit 15 5777 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5777) = 3 ^ 8 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5777.1, data_15_5777.2]

/-- Complete interval computation for depth 15, residue 5778. -/
theorem bounds_15_5778 : exactInterval 15 5778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5778 : oddCount 5778 15 = 8 ∧ acceleratedOrbit 15 5778 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5778) = 3 ^ 8 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5778.1, data_15_5778.2]

/-- Complete interval computation for depth 15, residue 5779. -/
theorem bounds_15_5779 : exactInterval 15 5779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5779 : oddCount 5779 15 = 8 ∧ acceleratedOrbit 15 5779 = 1160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5779) = 3 ^ 8 * m + 1160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5779.1, data_15_5779.2]

/-- Complete interval computation for depth 15, residue 5780. -/
theorem bounds_15_5780 : exactInterval 15 5780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5780 : oddCount 5780 15 = 5 ∧ acceleratedOrbit 15 5780 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5780) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5780.1, data_15_5780.2]

/-- Complete interval computation for depth 15, residue 5781. -/
theorem bounds_15_5781 : exactInterval 15 5781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5781 : oddCount 5781 15 = 5 ∧ acceleratedOrbit 15 5781 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5781) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5781.1, data_15_5781.2]

/-- Complete interval computation for depth 15, residue 5782. -/
theorem bounds_15_5782 : exactInterval 15 5782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5782 : oddCount 5782 15 = 5 ∧ acceleratedOrbit 15 5782 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5782) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5782.1, data_15_5782.2]

/-- Complete interval computation for depth 15, residue 5783. -/
theorem bounds_15_5783 : exactInterval 15 5783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5783 : oddCount 5783 15 = 5 ∧ acceleratedOrbit 15 5783 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5783) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5783.1, data_15_5783.2]

/-- Complete interval computation for depth 15, residue 5784. -/
theorem bounds_15_5784 : exactInterval 15 5784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5784 : oddCount 5784 15 = 5 ∧ acceleratedOrbit 15 5784 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5784) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5784.1, data_15_5784.2]

/-- Complete interval computation for depth 15, residue 5785. -/
theorem bounds_15_5785 : exactInterval 15 5785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5785 : oddCount 5785 15 = 9 ∧ acceleratedOrbit 15 5785 = 3478 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5785) = 3 ^ 9 * m + 3478 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5785.1, data_15_5785.2]

/-- Complete interval computation for depth 15, residue 5786. -/
theorem bounds_15_5786 : exactInterval 15 5786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5786 : oddCount 5786 15 = 5 ∧ acceleratedOrbit 15 5786 = 43 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5786) = 3 ^ 5 * m + 43 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5786.1, data_15_5786.2]

/-- Complete interval computation for depth 15, residue 5787. -/
theorem bounds_15_5787 : exactInterval 15 5787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5787 : oddCount 5787 15 = 8 ∧ acceleratedOrbit 15 5787 = 1159 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5787) = 3 ^ 8 * m + 1159 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5787.1, data_15_5787.2]

/-- Complete interval computation for depth 15, residue 5788. -/
theorem bounds_15_5788 : exactInterval 15 5788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5788 : oddCount 5788 15 = 9 ∧ acceleratedOrbit 15 5788 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5788) = 3 ^ 9 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5788.1, data_15_5788.2]

/-- Complete interval computation for depth 15, residue 5789. -/
theorem bounds_15_5789 : exactInterval 15 5789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5789 : oddCount 5789 15 = 9 ∧ acceleratedOrbit 15 5789 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5789) = 3 ^ 9 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5789.1, data_15_5789.2]

/-- Complete interval computation for depth 15, residue 5790. -/
theorem bounds_15_5790 : exactInterval 15 5790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5790 : oddCount 5790 15 = 9 ∧ acceleratedOrbit 15 5790 = 3482 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5790) = 3 ^ 9 * m + 3482 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5790.1, data_15_5790.2]

/-- Complete interval computation for depth 15, residue 5791. -/
theorem bounds_15_5791 : exactInterval 15 5791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5791 : oddCount 5791 15 = 11 ∧ acceleratedOrbit 15 5791 = 31313 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5791) = 3 ^ 11 * m + 31313 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5791.1, data_15_5791.2]

/-- Complete interval computation for depth 15, residue 5792. -/
theorem bounds_15_5792 : exactInterval 15 5792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5792 : oddCount 5792 15 = 3 ∧ acceleratedOrbit 15 5792 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5792) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5792.1, data_15_5792.2]

/-- Complete interval computation for depth 15, residue 5793. -/
theorem bounds_15_5793 : exactInterval 15 5793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5793 : oddCount 5793 15 = 10 ∧ acceleratedOrbit 15 5793 = 10448 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5793) = 3 ^ 10 * m + 10448 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5793.1, data_15_5793.2]

/-- Complete interval computation for depth 15, residue 5794. -/
theorem bounds_15_5794 : exactInterval 15 5794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5794 : oddCount 5794 15 = 8 ∧ acceleratedOrbit 15 5794 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5794) = 3 ^ 8 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5794.1, data_15_5794.2]

/-- Complete interval computation for depth 15, residue 5795. -/
theorem bounds_15_5795 : exactInterval 15 5795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5795 : oddCount 5795 15 = 8 ∧ acceleratedOrbit 15 5795 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5795) = 3 ^ 8 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5795.1, data_15_5795.2]

/-- Complete interval computation for depth 15, residue 5796. -/
theorem bounds_15_5796 : exactInterval 15 5796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5796 : oddCount 5796 15 = 8 ∧ acceleratedOrbit 15 5796 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5796) = 3 ^ 8 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5796.1, data_15_5796.2]

/-- Complete interval computation for depth 15, residue 5797. -/
theorem bounds_15_5797 : exactInterval 15 5797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5797 : oddCount 5797 15 = 8 ∧ acceleratedOrbit 15 5797 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5797) = 3 ^ 8 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5797.1, data_15_5797.2]

/-- Complete interval computation for depth 15, residue 5798. -/
theorem bounds_15_5798 : exactInterval 15 5798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5798 : oddCount 5798 15 = 8 ∧ acceleratedOrbit 15 5798 = 1162 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5798) = 3 ^ 8 * m + 1162 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5798.1, data_15_5798.2]

end Collatz.Research.PassageAtlas.Batch0177
