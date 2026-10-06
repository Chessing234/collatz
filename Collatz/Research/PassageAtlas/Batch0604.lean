import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0604

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19759. -/
theorem bounds_15_19759 : exactInterval 15 19759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19759 : oddCount 19759 15 = 11 ∧ acceleratedOrbit 15 19759 = 106829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19759) = 3 ^ 11 * m + 106829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19759.1, data_15_19759.2]

/-- Complete interval computation for depth 15, residue 19760. -/
theorem bounds_15_19760 : exactInterval 15 19760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19760 : oddCount 19760 15 = 7 ∧ acceleratedOrbit 15 19760 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19760) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19760.1, data_15_19760.2]

/-- Complete interval computation for depth 15, residue 19761. -/
theorem bounds_15_19761 : exactInterval 15 19761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19761 : oddCount 19761 15 = 8 ∧ acceleratedOrbit 15 19761 = 3959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19761) = 3 ^ 8 * m + 3959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19761.1, data_15_19761.2]

/-- Complete interval computation for depth 15, residue 19762. -/
theorem bounds_15_19762 : exactInterval 15 19762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19762 : oddCount 19762 15 = 8 ∧ acceleratedOrbit 15 19762 = 3959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19762) = 3 ^ 8 * m + 3959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19762.1, data_15_19762.2]

/-- Complete interval computation for depth 15, residue 19763. -/
theorem bounds_15_19763 : exactInterval 15 19763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19763 : oddCount 19763 15 = 8 ∧ acceleratedOrbit 15 19763 = 3959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19763) = 3 ^ 8 * m + 3959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19763.1, data_15_19763.2]

/-- Complete interval computation for depth 15, residue 19764. -/
theorem bounds_15_19764 : exactInterval 15 19764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19764 : oddCount 19764 15 = 7 ∧ acceleratedOrbit 15 19764 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19764) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19764.1, data_15_19764.2]

/-- Complete interval computation for depth 15, residue 19765. -/
theorem bounds_15_19765 : exactInterval 15 19765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19765 : oddCount 19765 15 = 7 ∧ acceleratedOrbit 15 19765 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19765) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19765.1, data_15_19765.2]

/-- Complete interval computation for depth 15, residue 19766. -/
theorem bounds_15_19766 : exactInterval 15 19766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19766 : oddCount 19766 15 = 9 ∧ acceleratedOrbit 15 19766 = 11875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19766) = 3 ^ 9 * m + 11875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19766.1, data_15_19766.2]

/-- Complete interval computation for depth 15, residue 19767. -/
theorem bounds_15_19767 : exactInterval 15 19767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19767 : oddCount 19767 15 = 9 ∧ acceleratedOrbit 15 19767 = 11875 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19767) = 3 ^ 9 * m + 11875 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19767.1, data_15_19767.2]

/-- Complete interval computation for depth 15, residue 19768. -/
theorem bounds_15_19768 : exactInterval 15 19768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19768 : oddCount 19768 15 = 6 ∧ acceleratedOrbit 15 19768 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19768) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19768.1, data_15_19768.2]

/-- Complete interval computation for depth 15, residue 19769. -/
theorem bounds_15_19769 : exactInterval 15 19769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19769 : oddCount 19769 15 = 10 ∧ acceleratedOrbit 15 19769 = 35630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19769) = 3 ^ 10 * m + 35630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19769.1, data_15_19769.2]

/-- Complete interval computation for depth 15, residue 19770. -/
theorem bounds_15_19770 : exactInterval 15 19770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19770 : oddCount 19770 15 = 6 ∧ acceleratedOrbit 15 19770 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19770) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19770.1, data_15_19770.2]

/-- Complete interval computation for depth 15, residue 19771. -/
theorem bounds_15_19771 : exactInterval 15 19771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19771 : oddCount 19771 15 = 7 ∧ acceleratedOrbit 15 19771 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19771) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19771.1, data_15_19771.2]

/-- Complete interval computation for depth 15, residue 19772. -/
theorem bounds_15_19772 : exactInterval 15 19772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19772 : oddCount 19772 15 = 6 ∧ acceleratedOrbit 15 19772 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19772) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19772.1, data_15_19772.2]

/-- Complete interval computation for depth 15, residue 19773. -/
theorem bounds_15_19773 : exactInterval 15 19773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19773 : oddCount 19773 15 = 6 ∧ acceleratedOrbit 15 19773 = 440 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19773) = 3 ^ 6 * m + 440 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19773.1, data_15_19773.2]

/-- Complete interval computation for depth 15, residue 19774. -/
theorem bounds_15_19774 : exactInterval 15 19774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19774 : oddCount 19774 15 = 11 ∧ acceleratedOrbit 15 19774 = 106913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19774) = 3 ^ 11 * m + 106913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19774.1, data_15_19774.2]

/-- Complete interval computation for depth 15, residue 19775. -/
theorem bounds_15_19775 : exactInterval 15 19775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19775 : oddCount 19775 15 = 11 ∧ acceleratedOrbit 15 19775 = 106913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19775) = 3 ^ 11 * m + 106913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19775.1, data_15_19775.2]

/-- Complete interval computation for depth 15, residue 19776. -/
theorem bounds_15_19776 : exactInterval 15 19776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19776 : oddCount 19776 15 = 3 ∧ acceleratedOrbit 15 19776 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19776) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19776.1, data_15_19776.2]

/-- Complete interval computation for depth 15, residue 19777. -/
theorem bounds_15_19777 : exactInterval 15 19777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19777 : oddCount 19777 15 = 7 ∧ acceleratedOrbit 15 19777 = 1322 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19777) = 3 ^ 7 * m + 1322 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19777.1, data_15_19777.2]

/-- Complete interval computation for depth 15, residue 19778. -/
theorem bounds_15_19778 : exactInterval 15 19778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19778 : oddCount 19778 15 = 8 ∧ acceleratedOrbit 15 19778 = 3962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19778) = 3 ^ 8 * m + 3962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19778.1, data_15_19778.2]

/-- Complete interval computation for depth 15, residue 19779. -/
theorem bounds_15_19779 : exactInterval 15 19779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19779 : oddCount 19779 15 = 8 ∧ acceleratedOrbit 15 19779 = 3962 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19779) = 3 ^ 8 * m + 3962 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19779.1, data_15_19779.2]

/-- Complete interval computation for depth 15, residue 19780. -/
theorem bounds_15_19780 : exactInterval 15 19780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19780 : oddCount 19780 15 = 8 ∧ acceleratedOrbit 15 19780 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19780) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19780.1, data_15_19780.2]

/-- Complete interval computation for depth 15, residue 19781. -/
theorem bounds_15_19781 : exactInterval 15 19781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19781 : oddCount 19781 15 = 8 ∧ acceleratedOrbit 15 19781 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19781) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19781.1, data_15_19781.2]

/-- Complete interval computation for depth 15, residue 19782. -/
theorem bounds_15_19782 : exactInterval 15 19782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19782 : oddCount 19782 15 = 8 ∧ acceleratedOrbit 15 19782 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19782) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19782.1, data_15_19782.2]

/-- Complete interval computation for depth 15, residue 19783. -/
theorem bounds_15_19783 : exactInterval 15 19783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19783 : oddCount 19783 15 = 10 ∧ acceleratedOrbit 15 19783 = 35653 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19783) = 3 ^ 10 * m + 35653 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19783.1, data_15_19783.2]

/-- Complete interval computation for depth 15, residue 19784. -/
theorem bounds_15_19784 : exactInterval 15 19784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19784 : oddCount 19784 15 = 8 ∧ acceleratedOrbit 15 19784 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19784) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19784.1, data_15_19784.2]

/-- Complete interval computation for depth 15, residue 19785. -/
theorem bounds_15_19785 : exactInterval 15 19785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19785 : oddCount 19785 15 = 10 ∧ acceleratedOrbit 15 19785 = 35660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19785) = 3 ^ 10 * m + 35660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19785.1, data_15_19785.2]

/-- Complete interval computation for depth 15, residue 19786. -/
theorem bounds_15_19786 : exactInterval 15 19786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19786 : oddCount 19786 15 = 8 ∧ acceleratedOrbit 15 19786 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19786) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19786.1, data_15_19786.2]

/-- Complete interval computation for depth 15, residue 19787. -/
theorem bounds_15_19787 : exactInterval 15 19787 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19787 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19787) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19787 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19787 : oddCount 19787 15 = 8 ∧ acceleratedOrbit 15 19787 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19787 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19787) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19787.1, data_15_19787.2]

/-- Complete interval computation for depth 15, residue 19788. -/
theorem bounds_15_19788 : exactInterval 15 19788 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19788 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19788) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19788 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19788 : oddCount 19788 15 = 8 ∧ acceleratedOrbit 15 19788 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19788 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19788) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19788.1, data_15_19788.2]

/-- Complete interval computation for depth 15, residue 19789. -/
theorem bounds_15_19789 : exactInterval 15 19789 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19789 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19789) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19789 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19789 : oddCount 19789 15 = 8 ∧ acceleratedOrbit 15 19789 = 3964 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19789 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19789) = 3 ^ 8 * m + 3964 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19789.1, data_15_19789.2]

/-- Complete interval computation for depth 15, residue 19790. -/
theorem bounds_15_19790 : exactInterval 15 19790 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19790 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19790) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19790 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19790 : oddCount 19790 15 = 7 ∧ acceleratedOrbit 15 19790 = 1321 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19790 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19790) = 3 ^ 7 * m + 1321 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19790.1, data_15_19790.2]

end Collatz.Research.PassageAtlas.Batch0604
