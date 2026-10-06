import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0299

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9764. -/
theorem bounds_15_9764 : exactInterval 15 9764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9764 : oddCount 9764 15 = 8 ∧ acceleratedOrbit 15 9764 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9764) = 3 ^ 8 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9764.1, data_15_9764.2]

/-- Complete interval computation for depth 15, residue 9765. -/
theorem bounds_15_9765 : exactInterval 15 9765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9765 : oddCount 9765 15 = 8 ∧ acceleratedOrbit 15 9765 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9765) = 3 ^ 8 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9765.1, data_15_9765.2]

/-- Complete interval computation for depth 15, residue 9766. -/
theorem bounds_15_9766 : exactInterval 15 9766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9766 : oddCount 9766 15 = 8 ∧ acceleratedOrbit 15 9766 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9766) = 3 ^ 8 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9766.1, data_15_9766.2]

/-- Complete interval computation for depth 15, residue 9767. -/
theorem bounds_15_9767 : exactInterval 15 9767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9767 : oddCount 9767 15 = 8 ∧ acceleratedOrbit 15 9767 = 1957 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9767) = 3 ^ 8 * m + 1957 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9767.1, data_15_9767.2]

/-- Complete interval computation for depth 15, residue 9768. -/
theorem bounds_15_9768 : exactInterval 15 9768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9768 : oddCount 9768 15 = 5 ∧ acceleratedOrbit 15 9768 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9768) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9768.1, data_15_9768.2]

/-- Complete interval computation for depth 15, residue 9769. -/
theorem bounds_15_9769 : exactInterval 15 9769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9769 : oddCount 9769 15 = 11 ∧ acceleratedOrbit 15 9769 = 52822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9769) = 3 ^ 11 * m + 52822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9769.1, data_15_9769.2]

/-- Complete interval computation for depth 15, residue 9770. -/
theorem bounds_15_9770 : exactInterval 15 9770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9770 : oddCount 9770 15 = 5 ∧ acceleratedOrbit 15 9770 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9770) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9770.1, data_15_9770.2]

/-- Complete interval computation for depth 15, residue 9771. -/
theorem bounds_15_9771 : exactInterval 15 9771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9771 : oddCount 9771 15 = 6 ∧ acceleratedOrbit 15 9771 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9771) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9771.1, data_15_9771.2]

/-- Complete interval computation for depth 15, residue 9772. -/
theorem bounds_15_9772 : exactInterval 15 9772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9772 : oddCount 9772 15 = 7 ∧ acceleratedOrbit 15 9772 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9772) = 3 ^ 7 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9772.1, data_15_9772.2]

/-- Complete interval computation for depth 15, residue 9773. -/
theorem bounds_15_9773 : exactInterval 15 9773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9773 : oddCount 9773 15 = 7 ∧ acceleratedOrbit 15 9773 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9773) = 3 ^ 7 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9773.1, data_15_9773.2]

/-- Complete interval computation for depth 15, residue 9774. -/
theorem bounds_15_9774 : exactInterval 15 9774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9774 : oddCount 9774 15 = 7 ∧ acceleratedOrbit 15 9774 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9774) = 3 ^ 7 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9774.1, data_15_9774.2]

/-- Complete interval computation for depth 15, residue 9775. -/
theorem bounds_15_9775 : exactInterval 15 9775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9775 : oddCount 9775 15 = 12 ∧ acceleratedOrbit 15 9775 = 158557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9775) = 3 ^ 12 * m + 158557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9775.1, data_15_9775.2]

/-- Complete interval computation for depth 15, residue 9776. -/
theorem bounds_15_9776 : exactInterval 15 9776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9776 : oddCount 9776 15 = 5 ∧ acceleratedOrbit 15 9776 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9776) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9776.1, data_15_9776.2]

/-- Complete interval computation for depth 15, residue 9777. -/
theorem bounds_15_9777 : exactInterval 15 9777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9777 : oddCount 9777 15 = 7 ∧ acceleratedOrbit 15 9777 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9777) = 3 ^ 7 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9777.1, data_15_9777.2]

/-- Complete interval computation for depth 15, residue 9778. -/
theorem bounds_15_9778 : exactInterval 15 9778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9778 : oddCount 9778 15 = 7 ∧ acceleratedOrbit 15 9778 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9778) = 3 ^ 7 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9778.1, data_15_9778.2]

/-- Complete interval computation for depth 15, residue 9779. -/
theorem bounds_15_9779 : exactInterval 15 9779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9779 : oddCount 9779 15 = 7 ∧ acceleratedOrbit 15 9779 = 653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9779) = 3 ^ 7 * m + 653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9779.1, data_15_9779.2]

/-- Complete interval computation for depth 15, residue 9780. -/
theorem bounds_15_9780 : exactInterval 15 9780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9780 : oddCount 9780 15 = 5 ∧ acceleratedOrbit 15 9780 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9780) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9780.1, data_15_9780.2]

/-- Complete interval computation for depth 15, residue 9781. -/
theorem bounds_15_9781 : exactInterval 15 9781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9781 : oddCount 9781 15 = 5 ∧ acceleratedOrbit 15 9781 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9781) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9781.1, data_15_9781.2]

/-- Complete interval computation for depth 15, residue 9782. -/
theorem bounds_15_9782 : exactInterval 15 9782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9782 : oddCount 9782 15 = 10 ∧ acceleratedOrbit 15 9782 = 17633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9782) = 3 ^ 10 * m + 17633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9782.1, data_15_9782.2]

/-- Complete interval computation for depth 15, residue 9783. -/
theorem bounds_15_9783 : exactInterval 15 9783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9783 : oddCount 9783 15 = 10 ∧ acceleratedOrbit 15 9783 = 17633 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9783) = 3 ^ 10 * m + 17633 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9783.1, data_15_9783.2]

/-- Complete interval computation for depth 15, residue 9784. -/
theorem bounds_15_9784 : exactInterval 15 9784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9784 : oddCount 9784 15 = 6 ∧ acceleratedOrbit 15 9784 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9784) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9784.1, data_15_9784.2]

/-- Complete interval computation for depth 15, residue 9785. -/
theorem bounds_15_9785 : exactInterval 15 9785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9785 : oddCount 9785 15 = 8 ∧ acceleratedOrbit 15 9785 = 1961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9785) = 3 ^ 8 * m + 1961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9785.1, data_15_9785.2]

/-- Complete interval computation for depth 15, residue 9786. -/
theorem bounds_15_9786 : exactInterval 15 9786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9786 : oddCount 9786 15 = 6 ∧ acceleratedOrbit 15 9786 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9786) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9786.1, data_15_9786.2]

/-- Complete interval computation for depth 15, residue 9787. -/
theorem bounds_15_9787 : exactInterval 15 9787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9787 : oddCount 9787 15 = 8 ∧ acceleratedOrbit 15 9787 = 1961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9787) = 3 ^ 8 * m + 1961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9787.1, data_15_9787.2]

/-- Complete interval computation for depth 15, residue 9788. -/
theorem bounds_15_9788 : exactInterval 15 9788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9788 : oddCount 9788 15 = 6 ∧ acceleratedOrbit 15 9788 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9788) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9788.1, data_15_9788.2]

/-- Complete interval computation for depth 15, residue 9789. -/
theorem bounds_15_9789 : exactInterval 15 9789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9789 : oddCount 9789 15 = 6 ∧ acceleratedOrbit 15 9789 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9789) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9789.1, data_15_9789.2]

/-- Complete interval computation for depth 15, residue 9790. -/
theorem bounds_15_9790 : exactInterval 15 9790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9790 : oddCount 9790 15 = 10 ∧ acceleratedOrbit 15 9790 = 17648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9790) = 3 ^ 10 * m + 17648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9790.1, data_15_9790.2]

/-- Complete interval computation for depth 15, residue 9791. -/
theorem bounds_15_9791 : exactInterval 15 9791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9791 : oddCount 9791 15 = 10 ∧ acceleratedOrbit 15 9791 = 17648 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9791) = 3 ^ 10 * m + 17648 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9791.1, data_15_9791.2]

/-- Complete interval computation for depth 15, residue 9792. -/
theorem bounds_15_9792 : exactInterval 15 9792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9792 : oddCount 9792 15 = 5 ∧ acceleratedOrbit 15 9792 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9792) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9792.1, data_15_9792.2]

/-- Complete interval computation for depth 15, residue 9793. -/
theorem bounds_15_9793 : exactInterval 15 9793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9793 : oddCount 9793 15 = 8 ∧ acceleratedOrbit 15 9793 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9793) = 3 ^ 8 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9793.1, data_15_9793.2]

/-- Complete interval computation for depth 15, residue 9794. -/
theorem bounds_15_9794 : exactInterval 15 9794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9794 : oddCount 9794 15 = 8 ∧ acceleratedOrbit 15 9794 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9794) = 3 ^ 8 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9794.1, data_15_9794.2]

/-- Complete interval computation for depth 15, residue 9795. -/
theorem bounds_15_9795 : exactInterval 15 9795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9795 : oddCount 9795 15 = 8 ∧ acceleratedOrbit 15 9795 = 1964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9795) = 3 ^ 8 * m + 1964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9795.1, data_15_9795.2]

/-- Complete interval computation for depth 15, residue 9796. -/
theorem bounds_15_9796 : exactInterval 15 9796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9796 : oddCount 9796 15 = 5 ∧ acceleratedOrbit 15 9796 = 73 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9796) = 3 ^ 5 * m + 73 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9796.1, data_15_9796.2]

end Collatz.Research.PassageAtlas.Batch0299
