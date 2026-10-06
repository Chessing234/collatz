import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0973

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7761. -/
theorem bounds_13_7761 : exactInterval 13 7761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7761 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7761) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7761 : oddCount 7761 13 = 6 ∧ acceleratedOrbit 13 7761 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7761 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7761) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7761.1, data_13_7761.2]

/-- Complete interval computation for depth 13, residue 7762. -/
theorem bounds_13_7762 : exactInterval 13 7762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7762 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7762) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7762 : oddCount 7762 13 = 6 ∧ acceleratedOrbit 13 7762 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7762 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7762) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7762.1, data_13_7762.2]

/-- Complete interval computation for depth 13, residue 7763. -/
theorem bounds_13_7763 : exactInterval 13 7763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7763 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7763) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7763 : oddCount 7763 13 = 6 ∧ acceleratedOrbit 13 7763 = 691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7763 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7763) = 3 ^ 6 * m + 691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7763.1, data_13_7763.2]

/-- Complete interval computation for depth 13, residue 7764. -/
theorem bounds_13_7764 : exactInterval 13 7764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7764 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7764) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7764 : oddCount 7764 13 = 5 ∧ acceleratedOrbit 13 7764 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7764 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7764) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7764.1, data_13_7764.2]

/-- Complete interval computation for depth 13, residue 7765. -/
theorem bounds_13_7765 : exactInterval 13 7765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7765 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7765) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7765 : oddCount 7765 13 = 5 ∧ acceleratedOrbit 13 7765 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7765 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7765) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7765.1, data_13_7765.2]

/-- Complete interval computation for depth 13, residue 7766. -/
theorem bounds_13_7766 : exactInterval 13 7766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7766 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7766) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7766 : oddCount 7766 13 = 6 ∧ acceleratedOrbit 13 7766 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7766 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7766) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7766.1, data_13_7766.2]

/-- Complete interval computation for depth 13, residue 7767. -/
theorem bounds_13_7767 : exactInterval 13 7767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7767 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7767) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7767 : oddCount 7767 13 = 6 ∧ acceleratedOrbit 13 7767 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7767 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7767) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7767.1, data_13_7767.2]

/-- Complete interval computation for depth 13, residue 7768. -/
theorem bounds_13_7768 : exactInterval 13 7768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7768 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7768) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7768 : oddCount 7768 13 = 4 ∧ acceleratedOrbit 13 7768 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7768 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7768) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7768.1, data_13_7768.2]

/-- Complete interval computation for depth 13, residue 7769. -/
theorem bounds_13_7769 : exactInterval 13 7769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7769 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7769) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7769 : oddCount 7769 13 = 8 ∧ acceleratedOrbit 13 7769 = 6227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7769 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7769) = 3 ^ 8 * m + 6227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7769.1, data_13_7769.2]

/-- Complete interval computation for depth 13, residue 7770. -/
theorem bounds_13_7770 : exactInterval 13 7770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7770 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7770) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7770 : oddCount 7770 13 = 4 ∧ acceleratedOrbit 13 7770 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7770 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7770) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7770.1, data_13_7770.2]

/-- Complete interval computation for depth 13, residue 7771. -/
theorem bounds_13_7771 : exactInterval 13 7771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7771 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7771) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7771 : oddCount 7771 13 = 7 ∧ acceleratedOrbit 13 7771 = 2075 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7771 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7771) = 3 ^ 7 * m + 2075 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7771.1, data_13_7771.2]

/-- Complete interval computation for depth 13, residue 7772. -/
theorem bounds_13_7772 : exactInterval 13 7772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7772 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7772) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7772 : oddCount 7772 13 = 4 ∧ acceleratedOrbit 13 7772 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7772 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7772) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7772.1, data_13_7772.2]

/-- Complete interval computation for depth 13, residue 7773. -/
theorem bounds_13_7773 : exactInterval 13 7773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7773 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7773) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7773 : oddCount 7773 13 = 4 ∧ acceleratedOrbit 13 7773 = 77 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7773 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7773) = 3 ^ 4 * m + 77 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7773.1, data_13_7773.2]

/-- Complete interval computation for depth 13, residue 7774. -/
theorem bounds_13_7774 : exactInterval 13 7774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7774 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7774) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7774 : oddCount 7774 13 = 6 ∧ acceleratedOrbit 13 7774 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7774 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7774) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7774.1, data_13_7774.2]

/-- Complete interval computation for depth 13, residue 7775. -/
theorem bounds_13_7775 : exactInterval 13 7775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7775 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7775) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7775 : oddCount 7775 13 = 6 ∧ acceleratedOrbit 13 7775 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7775 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7775) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7775.1, data_13_7775.2]

/-- Complete interval computation for depth 13, residue 7776. -/
theorem bounds_13_7776 : exactInterval 13 7776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7776 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7776) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7776 : oddCount 7776 13 = 5 ∧ acceleratedOrbit 13 7776 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7776 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7776) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7776.1, data_13_7776.2]

end Collatz.Research.StoppingAtlas.Batch0973
