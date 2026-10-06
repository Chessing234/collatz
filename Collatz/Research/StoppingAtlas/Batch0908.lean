import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0908

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6763. -/
theorem bounds_13_6763 : exactInterval 13 6763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6763 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6763) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6763 : oddCount 6763 13 = 6 ∧ acceleratedOrbit 13 6763 = 602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6763 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6763) = 3 ^ 6 * m + 602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6763.1, data_13_6763.2]

/-- Complete interval computation for depth 13, residue 6764. -/
theorem bounds_13_6764 : exactInterval 13 6764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6764 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6764) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6764 : oddCount 6764 13 = 8 ∧ acceleratedOrbit 13 6764 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6764 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6764) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6764.1, data_13_6764.2]

/-- Complete interval computation for depth 13, residue 6765. -/
theorem bounds_13_6765 : exactInterval 13 6765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6765 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6765) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6765 : oddCount 6765 13 = 8 ∧ acceleratedOrbit 13 6765 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6765 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6765) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6765.1, data_13_6765.2]

/-- Complete interval computation for depth 13, residue 6766. -/
theorem bounds_13_6766 : exactInterval 13 6766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6766 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6766) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6766 : oddCount 6766 13 = 8 ∧ acceleratedOrbit 13 6766 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6766 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6766) = 3 ^ 8 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6766.1, data_13_6766.2]

/-- Complete interval computation for depth 13, residue 6767. -/
theorem bounds_13_6767 : exactInterval 13 6767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6767 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6767) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6767 : oddCount 6767 13 = 10 ∧ acceleratedOrbit 13 6767 = 48788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6767 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6767) = 3 ^ 10 * m + 48788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6767.1, data_13_6767.2]

/-- Complete interval computation for depth 13, residue 6768. -/
theorem bounds_13_6768 : exactInterval 13 6768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6768 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6768) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6768 : oddCount 6768 13 = 6 ∧ acceleratedOrbit 13 6768 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6768 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6768) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6768.1, data_13_6768.2]

/-- Complete interval computation for depth 13, residue 6769. -/
theorem bounds_13_6769 : exactInterval 13 6769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6769 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6769) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6769 : oddCount 6769 13 = 5 ∧ acceleratedOrbit 13 6769 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6769 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6769) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6769.1, data_13_6769.2]

/-- Complete interval computation for depth 13, residue 6770. -/
theorem bounds_13_6770 : exactInterval 13 6770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6770 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6770) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6770 : oddCount 6770 13 = 9 ∧ acceleratedOrbit 13 6770 = 16280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6770 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6770) = 3 ^ 9 * m + 16280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6770.1, data_13_6770.2]

/-- Complete interval computation for depth 13, residue 6771. -/
theorem bounds_13_6771 : exactInterval 13 6771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6771 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6771) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6771 : oddCount 6771 13 = 9 ∧ acceleratedOrbit 13 6771 = 16280 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6771 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6771) = 3 ^ 9 * m + 16280 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6771.1, data_13_6771.2]

/-- Complete interval computation for depth 13, residue 6772. -/
theorem bounds_13_6772 : exactInterval 13 6772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6772 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6772) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6772 : oddCount 6772 13 = 6 ∧ acceleratedOrbit 13 6772 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6772 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6772) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6772.1, data_13_6772.2]

/-- Complete interval computation for depth 13, residue 6773. -/
theorem bounds_13_6773 : exactInterval 13 6773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6773 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6773) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6773 : oddCount 6773 13 = 6 ∧ acceleratedOrbit 13 6773 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6773 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6773) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6773.1, data_13_6773.2]

/-- Complete interval computation for depth 13, residue 6774. -/
theorem bounds_13_6774 : exactInterval 13 6774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6774 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6774) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6774 : oddCount 6774 13 = 4 ∧ acceleratedOrbit 13 6774 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6774 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6774) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6774.1, data_13_6774.2]

/-- Complete interval computation for depth 13, residue 6775. -/
theorem bounds_13_6775 : exactInterval 13 6775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6775 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6775) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6775 : oddCount 6775 13 = 4 ∧ acceleratedOrbit 13 6775 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6775 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6775) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6775.1, data_13_6775.2]

/-- Complete interval computation for depth 13, residue 6776. -/
theorem bounds_13_6776 : exactInterval 13 6776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6776 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6776) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6776 : oddCount 6776 13 = 6 ∧ acceleratedOrbit 13 6776 = 604 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6776 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6776) = 3 ^ 6 * m + 604 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6776.1, data_13_6776.2]

/-- Complete interval computation for depth 13, residue 6777. -/
theorem bounds_13_6777 : exactInterval 13 6777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6777 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6777) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6777 : oddCount 6777 13 = 7 ∧ acceleratedOrbit 13 6777 = 1810 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6777 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6777) = 3 ^ 7 * m + 1810 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6777.1, data_13_6777.2]

end Collatz.Research.StoppingAtlas.Batch0908
