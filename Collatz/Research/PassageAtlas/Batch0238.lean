import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0238

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7766. -/
theorem bounds_15_7766 : exactInterval 15 7766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7766 : oddCount 7766 15 = 6 ∧ acceleratedOrbit 15 7766 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7766) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7766.1, data_15_7766.2]

/-- Complete interval computation for depth 15, residue 7767. -/
theorem bounds_15_7767 : exactInterval 15 7767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7767 : oddCount 7767 15 = 6 ∧ acceleratedOrbit 15 7767 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7767) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7767.1, data_15_7767.2]

/-- Complete interval computation for depth 15, residue 7768. -/
theorem bounds_15_7768 : exactInterval 15 7768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7768 : oddCount 7768 15 = 5 ∧ acceleratedOrbit 15 7768 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7768) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7768.1, data_15_7768.2]

/-- Complete interval computation for depth 15, residue 7769. -/
theorem bounds_15_7769 : exactInterval 15 7769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7769 : oddCount 7769 15 = 10 ∧ acceleratedOrbit 15 7769 = 14012 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7769) = 3 ^ 10 * m + 14012 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7769.1, data_15_7769.2]

/-- Complete interval computation for depth 15, residue 7770. -/
theorem bounds_15_7770 : exactInterval 15 7770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7770 : oddCount 7770 15 = 5 ∧ acceleratedOrbit 15 7770 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7770) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7770.1, data_15_7770.2]

/-- Complete interval computation for depth 15, residue 7771. -/
theorem bounds_15_7771 : exactInterval 15 7771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7771 : oddCount 7771 15 = 9 ∧ acceleratedOrbit 15 7771 = 4670 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7771) = 3 ^ 9 * m + 4670 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7771.1, data_15_7771.2]

/-- Complete interval computation for depth 15, residue 7772. -/
theorem bounds_15_7772 : exactInterval 15 7772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7772 : oddCount 7772 15 = 5 ∧ acceleratedOrbit 15 7772 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7772) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7772.1, data_15_7772.2]

/-- Complete interval computation for depth 15, residue 7773. -/
theorem bounds_15_7773 : exactInterval 15 7773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7773 : oddCount 7773 15 = 5 ∧ acceleratedOrbit 15 7773 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7773) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7773.1, data_15_7773.2]

/-- Complete interval computation for depth 15, residue 7774. -/
theorem bounds_15_7774 : exactInterval 15 7774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7774 : oddCount 7774 15 = 6 ∧ acceleratedOrbit 15 7774 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7774) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7774.1, data_15_7774.2]

/-- Complete interval computation for depth 15, residue 7775. -/
theorem bounds_15_7775 : exactInterval 15 7775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7775 : oddCount 7775 15 = 6 ∧ acceleratedOrbit 15 7775 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7775) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7775.1, data_15_7775.2]

/-- Complete interval computation for depth 15, residue 7776. -/
theorem bounds_15_7776 : exactInterval 15 7776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7776 : oddCount 7776 15 = 6 ∧ acceleratedOrbit 15 7776 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7776) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7776.1, data_15_7776.2]

/-- Complete interval computation for depth 15, residue 7777. -/
theorem bounds_15_7777 : exactInterval 15 7777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7777 : oddCount 7777 15 = 8 ∧ acceleratedOrbit 15 7777 = 1559 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7777) = 3 ^ 8 * m + 1559 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7777.1, data_15_7777.2]

/-- Complete interval computation for depth 15, residue 7778. -/
theorem bounds_15_7778 : exactInterval 15 7778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7778 : oddCount 7778 15 = 5 ∧ acceleratedOrbit 15 7778 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7778) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7778.1, data_15_7778.2]

/-- Complete interval computation for depth 15, residue 7779. -/
theorem bounds_15_7779 : exactInterval 15 7779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7779 : oddCount 7779 15 = 5 ∧ acceleratedOrbit 15 7779 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7779) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7779.1, data_15_7779.2]

/-- Complete interval computation for depth 15, residue 7780. -/
theorem bounds_15_7780 : exactInterval 15 7780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7780 : oddCount 7780 15 = 5 ∧ acceleratedOrbit 15 7780 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7780) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7780.1, data_15_7780.2]

/-- Complete interval computation for depth 15, residue 7781. -/
theorem bounds_15_7781 : exactInterval 15 7781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7781 : oddCount 7781 15 = 5 ∧ acceleratedOrbit 15 7781 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7781) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7781.1, data_15_7781.2]

/-- Complete interval computation for depth 15, residue 7782. -/
theorem bounds_15_7782 : exactInterval 15 7782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7782 : oddCount 7782 15 = 5 ∧ acceleratedOrbit 15 7782 = 58 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7782) = 3 ^ 5 * m + 58 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7782.1, data_15_7782.2]

/-- Complete interval computation for depth 15, residue 7783. -/
theorem bounds_15_7783 : exactInterval 15 7783 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7783) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7783 : oddCount 7783 15 = 9 ∧ acceleratedOrbit 15 7783 = 4676 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7783) = 3 ^ 9 * m + 4676 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7783.1, data_15_7783.2]

/-- Complete interval computation for depth 15, residue 7784. -/
theorem bounds_15_7784 : exactInterval 15 7784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7784 : oddCount 7784 15 = 6 ∧ acceleratedOrbit 15 7784 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7784) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7784.1, data_15_7784.2]

/-- Complete interval computation for depth 15, residue 7785. -/
theorem bounds_15_7785 : exactInterval 15 7785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7785 : oddCount 7785 15 = 10 ∧ acceleratedOrbit 15 7785 = 14033 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7785) = 3 ^ 10 * m + 14033 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7785.1, data_15_7785.2]

/-- Complete interval computation for depth 15, residue 7786. -/
theorem bounds_15_7786 : exactInterval 15 7786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7786 : oddCount 7786 15 = 6 ∧ acceleratedOrbit 15 7786 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7786) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7786.1, data_15_7786.2]

/-- Complete interval computation for depth 15, residue 7787. -/
theorem bounds_15_7787 : exactInterval 15 7787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7787 : oddCount 7787 15 = 10 ∧ acceleratedOrbit 15 7787 = 14039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7787) = 3 ^ 10 * m + 14039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7787.1, data_15_7787.2]

/-- Complete interval computation for depth 15, residue 7788. -/
theorem bounds_15_7788 : exactInterval 15 7788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7788 : oddCount 7788 15 = 8 ∧ acceleratedOrbit 15 7788 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7788) = 3 ^ 8 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7788.1, data_15_7788.2]

/-- Complete interval computation for depth 15, residue 7789. -/
theorem bounds_15_7789 : exactInterval 15 7789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7789 : oddCount 7789 15 = 8 ∧ acceleratedOrbit 15 7789 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7789) = 3 ^ 8 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7789.1, data_15_7789.2]

/-- Complete interval computation for depth 15, residue 7790. -/
theorem bounds_15_7790 : exactInterval 15 7790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7790 : oddCount 7790 15 = 8 ∧ acceleratedOrbit 15 7790 = 1561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7790) = 3 ^ 8 * m + 1561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7790.1, data_15_7790.2]

/-- Complete interval computation for depth 15, residue 7791. -/
theorem bounds_15_7791 : exactInterval 15 7791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7791 : oddCount 7791 15 = 9 ∧ acceleratedOrbit 15 7791 = 4681 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7791) = 3 ^ 9 * m + 4681 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7791.1, data_15_7791.2]

/-- Complete interval computation for depth 15, residue 7792. -/
theorem bounds_15_7792 : exactInterval 15 7792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7792 : oddCount 7792 15 = 8 ∧ acceleratedOrbit 15 7792 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7792) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7792.1, data_15_7792.2]

/-- Complete interval computation for depth 15, residue 7793. -/
theorem bounds_15_7793 : exactInterval 15 7793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7793 : oddCount 7793 15 = 6 ∧ acceleratedOrbit 15 7793 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7793) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7793.1, data_15_7793.2]

/-- Complete interval computation for depth 15, residue 7794. -/
theorem bounds_15_7794 : exactInterval 15 7794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7794 : oddCount 7794 15 = 7 ∧ acceleratedOrbit 15 7794 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7794) = 3 ^ 7 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7794.1, data_15_7794.2]

/-- Complete interval computation for depth 15, residue 7795. -/
theorem bounds_15_7795 : exactInterval 15 7795 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7795 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7795) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7795 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7795 : oddCount 7795 15 = 7 ∧ acceleratedOrbit 15 7795 = 521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7795 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7795) = 3 ^ 7 * m + 521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7795.1, data_15_7795.2]

/-- Complete interval computation for depth 15, residue 7796. -/
theorem bounds_15_7796 : exactInterval 15 7796 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7796 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7796) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7796 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7796 : oddCount 7796 15 = 8 ∧ acceleratedOrbit 15 7796 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7796 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7796) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7796.1, data_15_7796.2]

/-- Complete interval computation for depth 15, residue 7797. -/
theorem bounds_15_7797 : exactInterval 15 7797 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7797 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7797) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7797 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7797 : oddCount 7797 15 = 8 ∧ acceleratedOrbit 15 7797 = 1565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7797 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7797) = 3 ^ 8 * m + 1565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7797.1, data_15_7797.2]

end Collatz.Research.PassageAtlas.Batch0238
