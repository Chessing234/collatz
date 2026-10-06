import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0482

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15761. -/
theorem bounds_15_15761 : exactInterval 15 15761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15761 : oddCount 15761 15 = 9 ∧ acceleratedOrbit 15 15761 = 9476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15761) = 3 ^ 9 * m + 9476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15761.1, data_15_15761.2]

/-- Complete interval computation for depth 15, residue 15762. -/
theorem bounds_15_15762 : exactInterval 15 15762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15762 : oddCount 15762 15 = 9 ∧ acceleratedOrbit 15 15762 = 9476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15762) = 3 ^ 9 * m + 9476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15762.1, data_15_15762.2]

/-- Complete interval computation for depth 15, residue 15763. -/
theorem bounds_15_15763 : exactInterval 15 15763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15763 : oddCount 15763 15 = 9 ∧ acceleratedOrbit 15 15763 = 9476 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15763) = 3 ^ 9 * m + 9476 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15763.1, data_15_15763.2]

/-- Complete interval computation for depth 15, residue 15764. -/
theorem bounds_15_15764 : exactInterval 15 15764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15764 : oddCount 15764 15 = 3 ∧ acceleratedOrbit 15 15764 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15764) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15764.1, data_15_15764.2]

/-- Complete interval computation for depth 15, residue 15765. -/
theorem bounds_15_15765 : exactInterval 15 15765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15765 : oddCount 15765 15 = 3 ∧ acceleratedOrbit 15 15765 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15765) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15765.1, data_15_15765.2]

/-- Complete interval computation for depth 15, residue 15766. -/
theorem bounds_15_15766 : exactInterval 15 15766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15766 : oddCount 15766 15 = 10 ∧ acceleratedOrbit 15 15766 = 28430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15766) = 3 ^ 10 * m + 28430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15766.1, data_15_15766.2]

/-- Complete interval computation for depth 15, residue 15767. -/
theorem bounds_15_15767 : exactInterval 15 15767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15767 : oddCount 15767 15 = 10 ∧ acceleratedOrbit 15 15767 = 28430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15767) = 3 ^ 10 * m + 28430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15767.1, data_15_15767.2]

/-- Complete interval computation for depth 15, residue 15768. -/
theorem bounds_15_15768 : exactInterval 15 15768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15768 : oddCount 15768 15 = 3 ∧ acceleratedOrbit 15 15768 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15768) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15768.1, data_15_15768.2]

/-- Complete interval computation for depth 15, residue 15769. -/
theorem bounds_15_15769 : exactInterval 15 15769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15769 : oddCount 15769 15 = 10 ∧ acceleratedOrbit 15 15769 = 28430 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15769) = 3 ^ 10 * m + 28430 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15769.1, data_15_15769.2]

/-- Complete interval computation for depth 15, residue 15770. -/
theorem bounds_15_15770 : exactInterval 15 15770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15770 : oddCount 15770 15 = 3 ∧ acceleratedOrbit 15 15770 = 13 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15770) = 3 ^ 3 * m + 13 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15770.1, data_15_15770.2]

/-- Complete interval computation for depth 15, residue 15771. -/
theorem bounds_15_15771 : exactInterval 15 15771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15771 : oddCount 15771 15 = 10 ∧ acceleratedOrbit 15 15771 = 28424 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15771) = 3 ^ 10 * m + 28424 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15771.1, data_15_15771.2]

/-- Complete interval computation for depth 15, residue 15772. -/
theorem bounds_15_15772 : exactInterval 15 15772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15772 : oddCount 15772 15 = 12 ∧ acceleratedOrbit 15 15772 = 255878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15772) = 3 ^ 12 * m + 255878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15772.1, data_15_15772.2]

/-- Complete interval computation for depth 15, residue 15773. -/
theorem bounds_15_15773 : exactInterval 15 15773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15773 : oddCount 15773 15 = 12 ∧ acceleratedOrbit 15 15773 = 255878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15773) = 3 ^ 12 * m + 255878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15773.1, data_15_15773.2]

/-- Complete interval computation for depth 15, residue 15774. -/
theorem bounds_15_15774 : exactInterval 15 15774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15774 : oddCount 15774 15 = 12 ∧ acceleratedOrbit 15 15774 = 255878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15774) = 3 ^ 12 * m + 255878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15774.1, data_15_15774.2]

/-- Complete interval computation for depth 15, residue 15775. -/
theorem bounds_15_15775 : exactInterval 15 15775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15775 : oddCount 15775 15 = 11 ∧ acceleratedOrbit 15 15775 = 85288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15775) = 3 ^ 11 * m + 85288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15775.1, data_15_15775.2]

/-- Complete interval computation for depth 15, residue 15776. -/
theorem bounds_15_15776 : exactInterval 15 15776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15776 : oddCount 15776 15 = 5 ∧ acceleratedOrbit 15 15776 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15776) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15776.1, data_15_15776.2]

/-- Complete interval computation for depth 15, residue 15777. -/
theorem bounds_15_15777 : exactInterval 15 15777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15777 : oddCount 15777 15 = 8 ∧ acceleratedOrbit 15 15777 = 3160 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15777) = 3 ^ 8 * m + 3160 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15777.1, data_15_15777.2]

/-- Complete interval computation for depth 15, residue 15778. -/
theorem bounds_15_15778 : exactInterval 15 15778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15778 : oddCount 15778 15 = 7 ∧ acceleratedOrbit 15 15778 = 1054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15778) = 3 ^ 7 * m + 1054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15778.1, data_15_15778.2]

/-- Complete interval computation for depth 15, residue 15779. -/
theorem bounds_15_15779 : exactInterval 15 15779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15779 : oddCount 15779 15 = 7 ∧ acceleratedOrbit 15 15779 = 1054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15779) = 3 ^ 7 * m + 1054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15779.1, data_15_15779.2]

/-- Complete interval computation for depth 15, residue 15780. -/
theorem bounds_15_15780 : exactInterval 15 15780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15780 : oddCount 15780 15 = 7 ∧ acceleratedOrbit 15 15780 = 1054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15780) = 3 ^ 7 * m + 1054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15780.1, data_15_15780.2]

/-- Complete interval computation for depth 15, residue 15781. -/
theorem bounds_15_15781 : exactInterval 15 15781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15781 : oddCount 15781 15 = 7 ∧ acceleratedOrbit 15 15781 = 1054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15781) = 3 ^ 7 * m + 1054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15781.1, data_15_15781.2]

/-- Complete interval computation for depth 15, residue 15782. -/
theorem bounds_15_15782 : exactInterval 15 15782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15782 : oddCount 15782 15 = 7 ∧ acceleratedOrbit 15 15782 = 1054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15782) = 3 ^ 7 * m + 1054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15782.1, data_15_15782.2]

/-- Complete interval computation for depth 15, residue 15783. -/
theorem bounds_15_15783 : exactInterval 15 15783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15783 : oddCount 15783 15 = 8 ∧ acceleratedOrbit 15 15783 = 3161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15783) = 3 ^ 8 * m + 3161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15783.1, data_15_15783.2]

/-- Complete interval computation for depth 15, residue 15784. -/
theorem bounds_15_15784 : exactInterval 15 15784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15784 : oddCount 15784 15 = 5 ∧ acceleratedOrbit 15 15784 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15784) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15784.1, data_15_15784.2]

/-- Complete interval computation for depth 15, residue 15785. -/
theorem bounds_15_15785 : exactInterval 15 15785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15785 : oddCount 15785 15 = 8 ∧ acceleratedOrbit 15 15785 = 3161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15785) = 3 ^ 8 * m + 3161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15785.1, data_15_15785.2]

/-- Complete interval computation for depth 15, residue 15786. -/
theorem bounds_15_15786 : exactInterval 15 15786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15786 : oddCount 15786 15 = 5 ∧ acceleratedOrbit 15 15786 = 118 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15786) = 3 ^ 5 * m + 118 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15786.1, data_15_15786.2]

/-- Complete interval computation for depth 15, residue 15787. -/
theorem bounds_15_15787 : exactInterval 15 15787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15787 : oddCount 15787 15 = 9 ∧ acceleratedOrbit 15 15787 = 9485 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15787) = 3 ^ 9 * m + 9485 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15787.1, data_15_15787.2]

/-- Complete interval computation for depth 15, residue 15788. -/
theorem bounds_15_15788 : exactInterval 15 15788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15788 : oddCount 15788 15 = 7 ∧ acceleratedOrbit 15 15788 = 1055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15788) = 3 ^ 7 * m + 1055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15788.1, data_15_15788.2]

/-- Complete interval computation for depth 15, residue 15789. -/
theorem bounds_15_15789 : exactInterval 15 15789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15789 : oddCount 15789 15 = 7 ∧ acceleratedOrbit 15 15789 = 1055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15789) = 3 ^ 7 * m + 1055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15789.1, data_15_15789.2]

/-- Complete interval computation for depth 15, residue 15790. -/
theorem bounds_15_15790 : exactInterval 15 15790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15790 : oddCount 15790 15 = 7 ∧ acceleratedOrbit 15 15790 = 1055 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15790) = 3 ^ 7 * m + 1055 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15790.1, data_15_15790.2]

/-- Complete interval computation for depth 15, residue 15791. -/
theorem bounds_15_15791 : exactInterval 15 15791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15791 : oddCount 15791 15 = 9 ∧ acceleratedOrbit 15 15791 = 9487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15791) = 3 ^ 9 * m + 9487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15791.1, data_15_15791.2]

/-- Complete interval computation for depth 15, residue 15792. -/
theorem bounds_15_15792 : exactInterval 15 15792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15792 : oddCount 15792 15 = 6 ∧ acceleratedOrbit 15 15792 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15792) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15792.1, data_15_15792.2]

/-- Complete interval computation for depth 15, residue 15793. -/
theorem bounds_15_15793 : exactInterval 15 15793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15793 : oddCount 15793 15 = 6 ∧ acceleratedOrbit 15 15793 = 352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15793) = 3 ^ 6 * m + 352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15793.1, data_15_15793.2]

end Collatz.Research.PassageAtlas.Batch0482
