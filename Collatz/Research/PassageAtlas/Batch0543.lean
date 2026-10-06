import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0543

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17760. -/
theorem bounds_15_17760 : exactInterval 15 17760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17760 : oddCount 17760 15 = 4 ∧ acceleratedOrbit 15 17760 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17760) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17760.1, data_15_17760.2]

/-- Complete interval computation for depth 15, residue 17761. -/
theorem bounds_15_17761 : exactInterval 15 17761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17761 : oddCount 17761 15 = 8 ∧ acceleratedOrbit 15 17761 = 3557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17761) = 3 ^ 8 * m + 3557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17761.1, data_15_17761.2]

/-- Complete interval computation for depth 15, residue 17762. -/
theorem bounds_15_17762 : exactInterval 15 17762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17762 : oddCount 17762 15 = 8 ∧ acceleratedOrbit 15 17762 = 3563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17762) = 3 ^ 8 * m + 3563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17762.1, data_15_17762.2]

/-- Complete interval computation for depth 15, residue 17763. -/
theorem bounds_15_17763 : exactInterval 15 17763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17763 : oddCount 17763 15 = 8 ∧ acceleratedOrbit 15 17763 = 3563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17763) = 3 ^ 8 * m + 3563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17763.1, data_15_17763.2]

/-- Complete interval computation for depth 15, residue 17764. -/
theorem bounds_15_17764 : exactInterval 15 17764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17764 : oddCount 17764 15 = 8 ∧ acceleratedOrbit 15 17764 = 3563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17764) = 3 ^ 8 * m + 3563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17764.1, data_15_17764.2]

/-- Complete interval computation for depth 15, residue 17765. -/
theorem bounds_15_17765 : exactInterval 15 17765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17765 : oddCount 17765 15 = 8 ∧ acceleratedOrbit 15 17765 = 3563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17765) = 3 ^ 8 * m + 3563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17765.1, data_15_17765.2]

/-- Complete interval computation for depth 15, residue 17766. -/
theorem bounds_15_17766 : exactInterval 15 17766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17766 : oddCount 17766 15 = 8 ∧ acceleratedOrbit 15 17766 = 3563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17766) = 3 ^ 8 * m + 3563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17766.1, data_15_17766.2]

/-- Complete interval computation for depth 15, residue 17767. -/
theorem bounds_15_17767 : exactInterval 15 17767 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17767) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17767 : oddCount 17767 15 = 9 ∧ acceleratedOrbit 15 17767 = 10673 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17767) = 3 ^ 9 * m + 10673 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17767.1, data_15_17767.2]

/-- Complete interval computation for depth 15, residue 17768. -/
theorem bounds_15_17768 : exactInterval 15 17768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17768 : oddCount 17768 15 = 4 ∧ acceleratedOrbit 15 17768 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17768) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17768.1, data_15_17768.2]

/-- Complete interval computation for depth 15, residue 17769. -/
theorem bounds_15_17769 : exactInterval 15 17769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17769 : oddCount 17769 15 = 8 ∧ acceleratedOrbit 15 17769 = 3559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17769) = 3 ^ 8 * m + 3559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17769.1, data_15_17769.2]

/-- Complete interval computation for depth 15, residue 17770. -/
theorem bounds_15_17770 : exactInterval 15 17770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17770 : oddCount 17770 15 = 4 ∧ acceleratedOrbit 15 17770 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17770) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17770.1, data_15_17770.2]

/-- Complete interval computation for depth 15, residue 17771. -/
theorem bounds_15_17771 : exactInterval 15 17771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17771 : oddCount 17771 15 = 8 ∧ acceleratedOrbit 15 17771 = 3559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17771) = 3 ^ 8 * m + 3559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17771.1, data_15_17771.2]

/-- Complete interval computation for depth 15, residue 17772. -/
theorem bounds_15_17772 : exactInterval 15 17772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17772 : oddCount 17772 15 = 7 ∧ acceleratedOrbit 15 17772 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17772) = 3 ^ 7 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17772.1, data_15_17772.2]

/-- Complete interval computation for depth 15, residue 17773. -/
theorem bounds_15_17773 : exactInterval 15 17773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17773 : oddCount 17773 15 = 7 ∧ acceleratedOrbit 15 17773 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17773) = 3 ^ 7 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17773.1, data_15_17773.2]

/-- Complete interval computation for depth 15, residue 17774. -/
theorem bounds_15_17774 : exactInterval 15 17774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17774 : oddCount 17774 15 = 7 ∧ acceleratedOrbit 15 17774 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17774) = 3 ^ 7 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17774.1, data_15_17774.2]

/-- Complete interval computation for depth 15, residue 17775. -/
theorem bounds_15_17775 : exactInterval 15 17775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17775 : oddCount 17775 15 = 10 ∧ acceleratedOrbit 15 17775 = 32035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17775) = 3 ^ 10 * m + 32035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17775.1, data_15_17775.2]

/-- Complete interval computation for depth 15, residue 17776. -/
theorem bounds_15_17776 : exactInterval 15 17776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17776 : oddCount 17776 15 = 4 ∧ acceleratedOrbit 15 17776 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17776) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17776.1, data_15_17776.2]

/-- Complete interval computation for depth 15, residue 17777. -/
theorem bounds_15_17777 : exactInterval 15 17777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17777 : oddCount 17777 15 = 4 ∧ acceleratedOrbit 15 17777 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17777) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17777.1, data_15_17777.2]

/-- Complete interval computation for depth 15, residue 17778. -/
theorem bounds_15_17778 : exactInterval 15 17778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17778 : oddCount 17778 15 = 8 ∧ acceleratedOrbit 15 17778 = 3563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17778) = 3 ^ 8 * m + 3563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17778.1, data_15_17778.2]

/-- Complete interval computation for depth 15, residue 17779. -/
theorem bounds_15_17779 : exactInterval 15 17779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17779 : oddCount 17779 15 = 8 ∧ acceleratedOrbit 15 17779 = 3563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17779) = 3 ^ 8 * m + 3563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17779.1, data_15_17779.2]

/-- Complete interval computation for depth 15, residue 17780. -/
theorem bounds_15_17780 : exactInterval 15 17780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17780 : oddCount 17780 15 = 4 ∧ acceleratedOrbit 15 17780 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17780) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17780.1, data_15_17780.2]

/-- Complete interval computation for depth 15, residue 17781. -/
theorem bounds_15_17781 : exactInterval 15 17781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17781 : oddCount 17781 15 = 4 ∧ acceleratedOrbit 15 17781 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17781) = 3 ^ 4 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17781.1, data_15_17781.2]

/-- Complete interval computation for depth 15, residue 17782. -/
theorem bounds_15_17782 : exactInterval 15 17782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17782 : oddCount 17782 15 = 9 ∧ acceleratedOrbit 15 17782 = 10685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17782) = 3 ^ 9 * m + 10685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17782.1, data_15_17782.2]

/-- Complete interval computation for depth 15, residue 17783. -/
theorem bounds_15_17783 : exactInterval 15 17783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17783 : oddCount 17783 15 = 9 ∧ acceleratedOrbit 15 17783 = 10685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17783) = 3 ^ 9 * m + 10685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17783.1, data_15_17783.2]

/-- Complete interval computation for depth 15, residue 17784. -/
theorem bounds_15_17784 : exactInterval 15 17784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17784 : oddCount 17784 15 = 9 ∧ acceleratedOrbit 15 17784 = 10691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17784) = 3 ^ 9 * m + 10691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17784.1, data_15_17784.2]

/-- Complete interval computation for depth 15, residue 17785. -/
theorem bounds_15_17785 : exactInterval 15 17785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17785 : oddCount 17785 15 = 11 ∧ acceleratedOrbit 15 17785 = 96160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17785) = 3 ^ 11 * m + 96160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17785.1, data_15_17785.2]

/-- Complete interval computation for depth 15, residue 17786. -/
theorem bounds_15_17786 : exactInterval 15 17786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17786 : oddCount 17786 15 = 9 ∧ acceleratedOrbit 15 17786 = 10691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17786) = 3 ^ 9 * m + 10691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17786.1, data_15_17786.2]

/-- Complete interval computation for depth 15, residue 17787. -/
theorem bounds_15_17787 : exactInterval 15 17787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17787 : oddCount 17787 15 = 8 ∧ acceleratedOrbit 15 17787 = 3563 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17787) = 3 ^ 8 * m + 3563 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17787.1, data_15_17787.2]

/-- Complete interval computation for depth 15, residue 17788. -/
theorem bounds_15_17788 : exactInterval 15 17788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17788 : oddCount 17788 15 = 9 ∧ acceleratedOrbit 15 17788 = 10691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17788) = 3 ^ 9 * m + 10691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17788.1, data_15_17788.2]

/-- Complete interval computation for depth 15, residue 17789. -/
theorem bounds_15_17789 : exactInterval 15 17789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17789 : oddCount 17789 15 = 9 ∧ acceleratedOrbit 15 17789 = 10691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17789) = 3 ^ 9 * m + 10691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17789.1, data_15_17789.2]

/-- Complete interval computation for depth 15, residue 17790. -/
theorem bounds_15_17790 : exactInterval 15 17790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17790 : oddCount 17790 15 = 11 ∧ acceleratedOrbit 15 17790 = 96187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17790) = 3 ^ 11 * m + 96187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17790.1, data_15_17790.2]

/-- Complete interval computation for depth 15, residue 17791. -/
theorem bounds_15_17791 : exactInterval 15 17791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17791 : oddCount 17791 15 = 11 ∧ acceleratedOrbit 15 17791 = 96187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17791) = 3 ^ 11 * m + 96187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17791.1, data_15_17791.2]

/-- Complete interval computation for depth 15, residue 17792. -/
theorem bounds_15_17792 : exactInterval 15 17792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17792 : oddCount 17792 15 = 5 ∧ acceleratedOrbit 15 17792 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17792) = 3 ^ 5 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17792.1, data_15_17792.2]

end Collatz.Research.PassageAtlas.Batch0543
