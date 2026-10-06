import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0421

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13762. -/
theorem bounds_15_13762 : exactInterval 15 13762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13762 : oddCount 13762 15 = 9 ∧ acceleratedOrbit 15 13762 = 8270 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13762) = 3 ^ 9 * m + 8270 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13762.1, data_15_13762.2]

/-- Complete interval computation for depth 15, residue 13763. -/
theorem bounds_15_13763 : exactInterval 15 13763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13763 : oddCount 13763 15 = 9 ∧ acceleratedOrbit 15 13763 = 8270 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13763) = 3 ^ 9 * m + 8270 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13763.1, data_15_13763.2]

/-- Complete interval computation for depth 15, residue 13764. -/
theorem bounds_15_13764 : exactInterval 15 13764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13764 : oddCount 13764 15 = 5 ∧ acceleratedOrbit 15 13764 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13764) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13764.1, data_15_13764.2]

/-- Complete interval computation for depth 15, residue 13765. -/
theorem bounds_15_13765 : exactInterval 15 13765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13765 : oddCount 13765 15 = 5 ∧ acceleratedOrbit 15 13765 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13765) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13765.1, data_15_13765.2]

/-- Complete interval computation for depth 15, residue 13766. -/
theorem bounds_15_13766 : exactInterval 15 13766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13766 : oddCount 13766 15 = 5 ∧ acceleratedOrbit 15 13766 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13766) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13766.1, data_15_13766.2]

/-- Complete interval computation for depth 15, residue 13767. -/
theorem bounds_15_13767 : exactInterval 15 13767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13767 : oddCount 13767 15 = 7 ∧ acceleratedOrbit 15 13767 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13767) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13767.1, data_15_13767.2]

/-- Complete interval computation for depth 15, residue 13768. -/
theorem bounds_15_13768 : exactInterval 15 13768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13768 : oddCount 13768 15 = 6 ∧ acceleratedOrbit 15 13768 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13768) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13768.1, data_15_13768.2]

/-- Complete interval computation for depth 15, residue 13769. -/
theorem bounds_15_13769 : exactInterval 15 13769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13769 : oddCount 13769 15 = 7 ∧ acceleratedOrbit 15 13769 = 920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13769) = 3 ^ 7 * m + 920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13769.1, data_15_13769.2]

/-- Complete interval computation for depth 15, residue 13770. -/
theorem bounds_15_13770 : exactInterval 15 13770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13770 : oddCount 13770 15 = 6 ∧ acceleratedOrbit 15 13770 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13770) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13770.1, data_15_13770.2]

/-- Complete interval computation for depth 15, residue 13771. -/
theorem bounds_15_13771 : exactInterval 15 13771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13771 : oddCount 13771 15 = 7 ∧ acceleratedOrbit 15 13771 = 920 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13771) = 3 ^ 7 * m + 920 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13771.1, data_15_13771.2]

/-- Complete interval computation for depth 15, residue 13772. -/
theorem bounds_15_13772 : exactInterval 15 13772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13772 : oddCount 13772 15 = 6 ∧ acceleratedOrbit 15 13772 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13772) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13772.1, data_15_13772.2]

/-- Complete interval computation for depth 15, residue 13773. -/
theorem bounds_15_13773 : exactInterval 15 13773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13773 : oddCount 13773 15 = 6 ∧ acceleratedOrbit 15 13773 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13773) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13773.1, data_15_13773.2]

/-- Complete interval computation for depth 15, residue 13774. -/
theorem bounds_15_13774 : exactInterval 15 13774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13774 : oddCount 13774 15 = 11 ∧ acceleratedOrbit 15 13774 = 74479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13774) = 3 ^ 11 * m + 74479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13774.1, data_15_13774.2]

/-- Complete interval computation for depth 15, residue 13775. -/
theorem bounds_15_13775 : exactInterval 15 13775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13775 : oddCount 13775 15 = 11 ∧ acceleratedOrbit 15 13775 = 74479 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13775) = 3 ^ 11 * m + 74479 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13775.1, data_15_13775.2]

/-- Complete interval computation for depth 15, residue 13776. -/
theorem bounds_15_13776 : exactInterval 15 13776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13776 : oddCount 13776 15 = 5 ∧ acceleratedOrbit 15 13776 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13776) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13776.1, data_15_13776.2]

/-- Complete interval computation for depth 15, residue 13777. -/
theorem bounds_15_13777 : exactInterval 15 13777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13777 : oddCount 13777 15 = 6 ∧ acceleratedOrbit 15 13777 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13777) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13777.1, data_15_13777.2]

/-- Complete interval computation for depth 15, residue 13778. -/
theorem bounds_15_13778 : exactInterval 15 13778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13778 : oddCount 13778 15 = 9 ∧ acceleratedOrbit 15 13778 = 8279 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13778) = 3 ^ 9 * m + 8279 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13778.1, data_15_13778.2]

/-- Complete interval computation for depth 15, residue 13779. -/
theorem bounds_15_13779 : exactInterval 15 13779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13779 : oddCount 13779 15 = 9 ∧ acceleratedOrbit 15 13779 = 8279 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13779) = 3 ^ 9 * m + 8279 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13779.1, data_15_13779.2]

/-- Complete interval computation for depth 15, residue 13780. -/
theorem bounds_15_13780 : exactInterval 15 13780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13780 : oddCount 13780 15 = 5 ∧ acceleratedOrbit 15 13780 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13780) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13780.1, data_15_13780.2]

/-- Complete interval computation for depth 15, residue 13781. -/
theorem bounds_15_13781 : exactInterval 15 13781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13781 : oddCount 13781 15 = 5 ∧ acceleratedOrbit 15 13781 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13781) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13781.1, data_15_13781.2]

/-- Complete interval computation for depth 15, residue 13782. -/
theorem bounds_15_13782 : exactInterval 15 13782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13782 : oddCount 13782 15 = 9 ∧ acceleratedOrbit 15 13782 = 8282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13782) = 3 ^ 9 * m + 8282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13782.1, data_15_13782.2]

/-- Complete interval computation for depth 15, residue 13783. -/
theorem bounds_15_13783 : exactInterval 15 13783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13783 : oddCount 13783 15 = 9 ∧ acceleratedOrbit 15 13783 = 8282 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13783) = 3 ^ 9 * m + 8282 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13783.1, data_15_13783.2]

/-- Complete interval computation for depth 15, residue 13784. -/
theorem bounds_15_13784 : exactInterval 15 13784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13784 : oddCount 13784 15 = 6 ∧ acceleratedOrbit 15 13784 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13784) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13784.1, data_15_13784.2]

/-- Complete interval computation for depth 15, residue 13785. -/
theorem bounds_15_13785 : exactInterval 15 13785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13785 : oddCount 13785 15 = 6 ∧ acceleratedOrbit 15 13785 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13785) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13785.1, data_15_13785.2]

/-- Complete interval computation for depth 15, residue 13786. -/
theorem bounds_15_13786 : exactInterval 15 13786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13786 : oddCount 13786 15 = 6 ∧ acceleratedOrbit 15 13786 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13786) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13786.1, data_15_13786.2]

/-- Complete interval computation for depth 15, residue 13787. -/
theorem bounds_15_13787 : exactInterval 15 13787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13787 : oddCount 13787 15 = 6 ∧ acceleratedOrbit 15 13787 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13787) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13787.1, data_15_13787.2]

/-- Complete interval computation for depth 15, residue 13788. -/
theorem bounds_15_13788 : exactInterval 15 13788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13788 : oddCount 13788 15 = 6 ∧ acceleratedOrbit 15 13788 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13788) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13788.1, data_15_13788.2]

/-- Complete interval computation for depth 15, residue 13789. -/
theorem bounds_15_13789 : exactInterval 15 13789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13789 : oddCount 13789 15 = 6 ∧ acceleratedOrbit 15 13789 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13789) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13789.1, data_15_13789.2]

/-- Complete interval computation for depth 15, residue 13790. -/
theorem bounds_15_13790 : exactInterval 15 13790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13790 : oddCount 13790 15 = 11 ∧ acceleratedOrbit 15 13790 = 74564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13790) = 3 ^ 11 * m + 74564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13790.1, data_15_13790.2]

/-- Complete interval computation for depth 15, residue 13791. -/
theorem bounds_15_13791 : exactInterval 15 13791 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13791 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13791) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13791 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13791 : oddCount 13791 15 = 11 ∧ acceleratedOrbit 15 13791 = 74564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13791 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13791) = 3 ^ 11 * m + 74564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13791.1, data_15_13791.2]

/-- Complete interval computation for depth 15, residue 13792. -/
theorem bounds_15_13792 : exactInterval 15 13792 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13792 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13792) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13792 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13792 : oddCount 13792 15 = 6 ∧ acceleratedOrbit 15 13792 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13792 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13792) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13792.1, data_15_13792.2]

/-- Complete interval computation for depth 15, residue 13793. -/
theorem bounds_15_13793 : exactInterval 15 13793 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13793 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13793) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13793 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13793 : oddCount 13793 15 = 9 ∧ acceleratedOrbit 15 13793 = 8288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13793 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13793) = 3 ^ 9 * m + 8288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13793.1, data_15_13793.2]

/-- Complete interval computation for depth 15, residue 13794. -/
theorem bounds_15_13794 : exactInterval 15 13794 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13794 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13794) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13794 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13794 : oddCount 13794 15 = 5 ∧ acceleratedOrbit 15 13794 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13794 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13794) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13794.1, data_15_13794.2]

end Collatz.Research.PassageAtlas.Batch0421
