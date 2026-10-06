import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0776

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4736. -/
theorem bounds_13_4736 : exactInterval 13 4736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4736 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4736) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4736 : oddCount 4736 13 = 3 ∧ acceleratedOrbit 13 4736 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4736 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4736) = 3 ^ 3 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4736.1, data_13_4736.2]

/-- Complete interval computation for depth 13, residue 4737. -/
theorem bounds_13_4737 : exactInterval 13 4737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4737 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4737) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4737 : oddCount 4737 13 = 8 ∧ acceleratedOrbit 13 4737 = 3797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4737 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4737) = 3 ^ 8 * m + 3797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4737.1, data_13_4737.2]

/-- Complete interval computation for depth 13, residue 4738. -/
theorem bounds_13_4738 : exactInterval 13 4738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4738 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4738) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4738 : oddCount 4738 13 = 4 ∧ acceleratedOrbit 13 4738 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4738 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4738) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4738.1, data_13_4738.2]

/-- Complete interval computation for depth 13, residue 4739. -/
theorem bounds_13_4739 : exactInterval 13 4739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4739 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4739) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4739 : oddCount 4739 13 = 4 ∧ acceleratedOrbit 13 4739 = 47 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4739 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4739) = 3 ^ 4 * m + 47 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4739.1, data_13_4739.2]

/-- Complete interval computation for depth 13, residue 4740. -/
theorem bounds_13_4740 : exactInterval 13 4740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4740 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4740) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4740 : oddCount 4740 13 = 8 ∧ acceleratedOrbit 13 4740 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4740 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4740) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4740.1, data_13_4740.2]

/-- Complete interval computation for depth 13, residue 4741. -/
theorem bounds_13_4741 : exactInterval 13 4741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4741 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4741) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4741 : oddCount 4741 13 = 8 ∧ acceleratedOrbit 13 4741 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4741 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4741) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4741.1, data_13_4741.2]

/-- Complete interval computation for depth 13, residue 4742. -/
theorem bounds_13_4742 : exactInterval 13 4742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4742 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4742) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4742 : oddCount 4742 13 = 8 ∧ acceleratedOrbit 13 4742 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4742 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4742) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4742.1, data_13_4742.2]

/-- Complete interval computation for depth 13, residue 4743. -/
theorem bounds_13_4743 : exactInterval 13 4743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4743 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4743) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4743 : oddCount 4743 13 = 7 ∧ acceleratedOrbit 13 4743 = 1268 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4743 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4743) = 3 ^ 7 * m + 1268 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4743.1, data_13_4743.2]

/-- Complete interval computation for depth 13, residue 4744. -/
theorem bounds_13_4744 : exactInterval 13 4744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4744 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4744) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4744 : oddCount 4744 13 = 6 ∧ acceleratedOrbit 13 4744 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4744 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4744) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4744.1, data_13_4744.2]

/-- Complete interval computation for depth 13, residue 4745. -/
theorem bounds_13_4745 : exactInterval 13 4745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4745 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4745) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4745 : oddCount 4745 13 = 8 ∧ acceleratedOrbit 13 4745 = 3802 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4745 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4745) = 3 ^ 8 * m + 3802 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4745.1, data_13_4745.2]

/-- Complete interval computation for depth 13, residue 4746. -/
theorem bounds_13_4746 : exactInterval 13 4746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4746 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4746) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4746 : oddCount 4746 13 = 6 ∧ acceleratedOrbit 13 4746 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4746 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4746) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4746.1, data_13_4746.2]

/-- Complete interval computation for depth 13, residue 4747. -/
theorem bounds_13_4747 : exactInterval 13 4747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4747 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4747) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4747 : oddCount 4747 13 = 8 ∧ acceleratedOrbit 13 4747 = 3806 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4747 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4747) = 3 ^ 8 * m + 3806 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4747.1, data_13_4747.2]

/-- Complete interval computation for depth 13, residue 4748. -/
theorem bounds_13_4748 : exactInterval 13 4748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4748 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4748) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4748 : oddCount 4748 13 = 6 ∧ acceleratedOrbit 13 4748 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4748 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4748) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4748.1, data_13_4748.2]

/-- Complete interval computation for depth 13, residue 4749. -/
theorem bounds_13_4749 : exactInterval 13 4749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4749 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4749) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4749 : oddCount 4749 13 = 6 ∧ acceleratedOrbit 13 4749 = 425 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4749 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4749) = 3 ^ 6 * m + 425 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4749.1, data_13_4749.2]

/-- Complete interval computation for depth 13, residue 4750. -/
theorem bounds_13_4750 : exactInterval 13 4750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4750 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4750) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4750 : oddCount 4750 13 = 10 ∧ acceleratedOrbit 13 4750 = 34262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4750 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4750) = 3 ^ 10 * m + 34262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4750.1, data_13_4750.2]

end Collatz.Research.StoppingAtlas.Batch0776
