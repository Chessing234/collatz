import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0049

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 737. -/
theorem bounds_10_737 : exactInterval 10 737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_737 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 737) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_737 : oddCount 737 10 = 7 ∧ acceleratedOrbit 10 737 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_737 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 737) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_737.1, data_10_737.2]

/-- Complete interval computation for depth 10, residue 738. -/
theorem bounds_10_738 : exactInterval 10 738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_738 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 738) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_738 : oddCount 738 10 = 3 ∧ acceleratedOrbit 10 738 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_738 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 738) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_738.1, data_10_738.2]

/-- Complete interval computation for depth 10, residue 739. -/
theorem bounds_10_739 : exactInterval 10 739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_739 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 739) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_739 : oddCount 739 10 = 3 ∧ acceleratedOrbit 10 739 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_739 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 739) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_739.1, data_10_739.2]

/-- Complete interval computation for depth 10, residue 740. -/
theorem bounds_10_740 : exactInterval 10 740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_740 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 740) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_740 : oddCount 740 10 = 4 ∧ acceleratedOrbit 10 740 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_740 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 740) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_740.1, data_10_740.2]

/-- Complete interval computation for depth 10, residue 741. -/
theorem bounds_10_741 : exactInterval 10 741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_741 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 741) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_741 : oddCount 741 10 = 4 ∧ acceleratedOrbit 10 741 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_741 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 741) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_741.1, data_10_741.2]

/-- Complete interval computation for depth 10, residue 742. -/
theorem bounds_10_742 : exactInterval 10 742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_742 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 742) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_742 : oddCount 742 10 = 4 ∧ acceleratedOrbit 10 742 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_742 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 742) = 3 ^ 4 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_742.1, data_10_742.2]

/-- Complete interval computation for depth 10, residue 743. -/
theorem bounds_10_743 : exactInterval 10 743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_743 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 743) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_743 : oddCount 743 10 = 8 ∧ acceleratedOrbit 10 743 = 4769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_743 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 743) = 3 ^ 8 * m + 4769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_743.1, data_10_743.2]

/-- Complete interval computation for depth 10, residue 744. -/
theorem bounds_10_744 : exactInterval 10 744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_744 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 744) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_744 : oddCount 744 10 = 3 ∧ acceleratedOrbit 10 744 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_744 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 744) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_744.1, data_10_744.2]

/-- Complete interval computation for depth 10, residue 745. -/
theorem bounds_10_745 : exactInterval 10 745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_745 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 745) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_745 : oddCount 745 10 = 7 ∧ acceleratedOrbit 10 745 = 1595 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_745 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 745) = 3 ^ 7 * m + 1595 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_745.1, data_10_745.2]

/-- Complete interval computation for depth 10, residue 746. -/
theorem bounds_10_746 : exactInterval 10 746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_746 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 746) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_746 : oddCount 746 10 = 3 ∧ acceleratedOrbit 10 746 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_746 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 746) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_746.1, data_10_746.2]

/-- Complete interval computation for depth 10, residue 747. -/
theorem bounds_10_747 : exactInterval 10 747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_747 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 747) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_747 : oddCount 747 10 = 6 ∧ acceleratedOrbit 10 747 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_747 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 747) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_747.1, data_10_747.2]

/-- Complete interval computation for depth 10, residue 748. -/
theorem bounds_10_748 : exactInterval 10 748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_748 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 748) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_748 : oddCount 748 10 = 5 ∧ acceleratedOrbit 10 748 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_748 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 748) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_748.1, data_10_748.2]

/-- Complete interval computation for depth 10, residue 749. -/
theorem bounds_10_749 : exactInterval 10 749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_749 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 749) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_749 : oddCount 749 10 = 5 ∧ acceleratedOrbit 10 749 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_749 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 749) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_749.1, data_10_749.2]

/-- Complete interval computation for depth 10, residue 750. -/
theorem bounds_10_750 : exactInterval 10 750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_750 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 750) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_750 : oddCount 750 10 = 5 ∧ acceleratedOrbit 10 750 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_750 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 750) = 3 ^ 5 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_750.1, data_10_750.2]

/-- Complete interval computation for depth 10, residue 751. -/
theorem bounds_10_751 : exactInterval 10 751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_751 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 751) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_751 : oddCount 751 10 = 8 ∧ acceleratedOrbit 10 751 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_751 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 751) = 3 ^ 8 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_751.1, data_10_751.2]

end Collatz.Research.StoppingAtlas.Batch0049
