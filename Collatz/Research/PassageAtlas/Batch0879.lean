import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0879

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 28770. -/
theorem bounds_15_28770 : exactInterval 15 28770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28770 : oddCount 28770 15 = 8 ∧ acceleratedOrbit 15 28770 = 5764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28770) = 3 ^ 8 * m + 5764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28770.1, data_15_28770.2]

/-- Complete interval computation for depth 15, residue 28771. -/
theorem bounds_15_28771 : exactInterval 15 28771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28771 : oddCount 28771 15 = 8 ∧ acceleratedOrbit 15 28771 = 5764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28771) = 3 ^ 8 * m + 5764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28771.1, data_15_28771.2]

/-- Complete interval computation for depth 15, residue 28772. -/
theorem bounds_15_28772 : exactInterval 15 28772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28772 : oddCount 28772 15 = 8 ∧ acceleratedOrbit 15 28772 = 5764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28772) = 3 ^ 8 * m + 5764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28772.1, data_15_28772.2]

/-- Complete interval computation for depth 15, residue 28773. -/
theorem bounds_15_28773 : exactInterval 15 28773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28773 : oddCount 28773 15 = 8 ∧ acceleratedOrbit 15 28773 = 5764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28773) = 3 ^ 8 * m + 5764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28773.1, data_15_28773.2]

/-- Complete interval computation for depth 15, residue 28774. -/
theorem bounds_15_28774 : exactInterval 15 28774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28774 : oddCount 28774 15 = 8 ∧ acceleratedOrbit 15 28774 = 5764 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28774) = 3 ^ 8 * m + 5764 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28774.1, data_15_28774.2]

/-- Complete interval computation for depth 15, residue 28775. -/
theorem bounds_15_28775 : exactInterval 15 28775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28775 : oddCount 28775 15 = 10 ∧ acceleratedOrbit 15 28775 = 51857 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28775) = 3 ^ 10 * m + 51857 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28775.1, data_15_28775.2]

/-- Complete interval computation for depth 15, residue 28776. -/
theorem bounds_15_28776 : exactInterval 15 28776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28776 : oddCount 28776 15 = 5 ∧ acceleratedOrbit 15 28776 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28776) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28776.1, data_15_28776.2]

/-- Complete interval computation for depth 15, residue 28777. -/
theorem bounds_15_28777 : exactInterval 15 28777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28777 : oddCount 28777 15 = 7 ∧ acceleratedOrbit 15 28777 = 1921 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28777) = 3 ^ 7 * m + 1921 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28777.1, data_15_28777.2]

/-- Complete interval computation for depth 15, residue 28778. -/
theorem bounds_15_28778 : exactInterval 15 28778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28778 : oddCount 28778 15 = 5 ∧ acceleratedOrbit 15 28778 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28778) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28778.1, data_15_28778.2]

/-- Complete interval computation for depth 15, residue 28779. -/
theorem bounds_15_28779 : exactInterval 15 28779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28779 : oddCount 28779 15 = 10 ∧ acceleratedOrbit 15 28779 = 51866 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28779) = 3 ^ 10 * m + 51866 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28779.1, data_15_28779.2]

/-- Complete interval computation for depth 15, residue 28780. -/
theorem bounds_15_28780 : exactInterval 15 28780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28780 : oddCount 28780 15 = 9 ∧ acceleratedOrbit 15 28780 = 17291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28780) = 3 ^ 9 * m + 17291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28780.1, data_15_28780.2]

/-- Complete interval computation for depth 15, residue 28781. -/
theorem bounds_15_28781 : exactInterval 15 28781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28781 : oddCount 28781 15 = 9 ∧ acceleratedOrbit 15 28781 = 17291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28781) = 3 ^ 9 * m + 17291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28781.1, data_15_28781.2]

/-- Complete interval computation for depth 15, residue 28782. -/
theorem bounds_15_28782 : exactInterval 15 28782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28782 : oddCount 28782 15 = 9 ∧ acceleratedOrbit 15 28782 = 17291 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28782) = 3 ^ 9 * m + 17291 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28782.1, data_15_28782.2]

/-- Complete interval computation for depth 15, residue 28783. -/
theorem bounds_15_28783 : exactInterval 15 28783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28783 : oddCount 28783 15 = 11 ∧ acceleratedOrbit 15 28783 = 155611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28783) = 3 ^ 11 * m + 155611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28783.1, data_15_28783.2]

/-- Complete interval computation for depth 15, residue 28784. -/
theorem bounds_15_28784 : exactInterval 15 28784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28784 : oddCount 28784 15 = 6 ∧ acceleratedOrbit 15 28784 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28784) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28784.1, data_15_28784.2]

/-- Complete interval computation for depth 15, residue 28785. -/
theorem bounds_15_28785 : exactInterval 15 28785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28785 : oddCount 28785 15 = 5 ∧ acceleratedOrbit 15 28785 = 215 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28785) = 3 ^ 5 * m + 215 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28785.1, data_15_28785.2]

/-- Complete interval computation for depth 15, residue 28786. -/
theorem bounds_15_28786 : exactInterval 15 28786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28786 : oddCount 28786 15 = 6 ∧ acceleratedOrbit 15 28786 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28786) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28786.1, data_15_28786.2]

/-- Complete interval computation for depth 15, residue 28787. -/
theorem bounds_15_28787 : exactInterval 15 28787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28787 : oddCount 28787 15 = 6 ∧ acceleratedOrbit 15 28787 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28787) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28787.1, data_15_28787.2]

/-- Complete interval computation for depth 15, residue 28788. -/
theorem bounds_15_28788 : exactInterval 15 28788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28788 : oddCount 28788 15 = 6 ∧ acceleratedOrbit 15 28788 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28788) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28788.1, data_15_28788.2]

/-- Complete interval computation for depth 15, residue 28789. -/
theorem bounds_15_28789 : exactInterval 15 28789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28789 : oddCount 28789 15 = 6 ∧ acceleratedOrbit 15 28789 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28789) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28789.1, data_15_28789.2]

/-- Complete interval computation for depth 15, residue 28790. -/
theorem bounds_15_28790 : exactInterval 15 28790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28790 : oddCount 28790 15 = 7 ∧ acceleratedOrbit 15 28790 = 1922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28790) = 3 ^ 7 * m + 1922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28790.1, data_15_28790.2]

/-- Complete interval computation for depth 15, residue 28791. -/
theorem bounds_15_28791 : exactInterval 15 28791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28791 : oddCount 28791 15 = 7 ∧ acceleratedOrbit 15 28791 = 1922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28791) = 3 ^ 7 * m + 1922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28791.1, data_15_28791.2]

/-- Complete interval computation for depth 15, residue 28792. -/
theorem bounds_15_28792 : exactInterval 15 28792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28792 : oddCount 28792 15 = 6 ∧ acceleratedOrbit 15 28792 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28792) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28792.1, data_15_28792.2]

/-- Complete interval computation for depth 15, residue 28793. -/
theorem bounds_15_28793 : exactInterval 15 28793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28793 : oddCount 28793 15 = 11 ∧ acceleratedOrbit 15 28793 = 155672 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28793) = 3 ^ 11 * m + 155672 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28793.1, data_15_28793.2]

/-- Complete interval computation for depth 15, residue 28794. -/
theorem bounds_15_28794 : exactInterval 15 28794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28794 : oddCount 28794 15 = 6 ∧ acceleratedOrbit 15 28794 = 641 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28794) = 3 ^ 6 * m + 641 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28794.1, data_15_28794.2]

/-- Complete interval computation for depth 15, residue 28795. -/
theorem bounds_15_28795 : exactInterval 15 28795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28795 : oddCount 28795 15 = 7 ∧ acceleratedOrbit 15 28795 = 1922 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28795) = 3 ^ 7 * m + 1922 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28795.1, data_15_28795.2]

/-- Complete interval computation for depth 15, residue 28796. -/
theorem bounds_15_28796 : exactInterval 15 28796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28796 : oddCount 28796 15 = 9 ∧ acceleratedOrbit 15 28796 = 17300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28796) = 3 ^ 9 * m + 17300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28796.1, data_15_28796.2]

/-- Complete interval computation for depth 15, residue 28797. -/
theorem bounds_15_28797 : exactInterval 15 28797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28797 : oddCount 28797 15 = 9 ∧ acceleratedOrbit 15 28797 = 17300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28797) = 3 ^ 9 * m + 17300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28797.1, data_15_28797.2]

/-- Complete interval computation for depth 15, residue 28798. -/
theorem bounds_15_28798 : exactInterval 15 28798 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28798 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28798) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28798 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28798 : oddCount 28798 15 = 9 ∧ acceleratedOrbit 15 28798 = 17300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28798 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28798) = 3 ^ 9 * m + 17300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28798.1, data_15_28798.2]

/-- Complete interval computation for depth 15, residue 28799. -/
theorem bounds_15_28799 : exactInterval 15 28799 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28799 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28799) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28799 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28799 : oddCount 28799 15 = 9 ∧ acceleratedOrbit 15 28799 = 17300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28799 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28799) = 3 ^ 9 * m + 17300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28799.1, data_15_28799.2]

/-- Complete interval computation for depth 15, residue 28800. -/
theorem bounds_15_28800 : exactInterval 15 28800 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28800 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28800) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28800 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28800 : oddCount 28800 15 = 6 ∧ acceleratedOrbit 15 28800 = 647 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28800 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28800) = 3 ^ 6 * m + 647 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28800.1, data_15_28800.2]

/-- Complete interval computation for depth 15, residue 28801. -/
theorem bounds_15_28801 : exactInterval 15 28801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28801 : oddCount 28801 15 = 8 ∧ acceleratedOrbit 15 28801 = 5768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28801) = 3 ^ 8 * m + 5768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28801.1, data_15_28801.2]

/-- Complete interval computation for depth 15, residue 28802. -/
theorem bounds_15_28802 : exactInterval 15 28802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_28802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 28802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_28802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_28802 : oddCount 28802 15 = 8 ∧ acceleratedOrbit 15 28802 = 5771 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_28802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 28802) = 3 ^ 8 * m + 5771 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_28802.1, data_15_28802.2]

end Collatz.Research.PassageAtlas.Batch0879
