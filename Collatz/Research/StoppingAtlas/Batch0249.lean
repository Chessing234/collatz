import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0249

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 737. -/
theorem bounds_12_737 : exactInterval 12 737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_737 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 737) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_737 : oddCount 737 12 = 9 ∧ acceleratedOrbit 12 737 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_737 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 737) = 3 ^ 9 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_737.1, data_12_737.2]

/-- Complete interval computation for depth 12, residue 738. -/
theorem bounds_12_738 : exactInterval 12 738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_738 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 738) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_738 : oddCount 738 12 = 3 ∧ acceleratedOrbit 12 738 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_738 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 738) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_738.1, data_12_738.2]

/-- Complete interval computation for depth 12, residue 739. -/
theorem bounds_12_739 : exactInterval 12 739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_739 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 739) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_739 : oddCount 739 12 = 3 ∧ acceleratedOrbit 12 739 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_739 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 739) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_739.1, data_12_739.2]

/-- Complete interval computation for depth 12, residue 740. -/
theorem bounds_12_740 : exactInterval 12 740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_740 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 740) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_740 : oddCount 740 12 = 6 ∧ acceleratedOrbit 12 740 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_740 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 740) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_740.1, data_12_740.2]

/-- Complete interval computation for depth 12, residue 741. -/
theorem bounds_12_741 : exactInterval 12 741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_741 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 741) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_741 : oddCount 741 12 = 6 ∧ acceleratedOrbit 12 741 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_741 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 741) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_741.1, data_12_741.2]

/-- Complete interval computation for depth 12, residue 742. -/
theorem bounds_12_742 : exactInterval 12 742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_742 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 742) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_742 : oddCount 742 12 = 6 ∧ acceleratedOrbit 12 742 = 134 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_742 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 742) = 3 ^ 6 * m + 134 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_742.1, data_12_742.2]

/-- Complete interval computation for depth 12, residue 743. -/
theorem bounds_12_743 : exactInterval 12 743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_743 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 743) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_743 : oddCount 743 12 = 9 ∧ acceleratedOrbit 12 743 = 3577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_743 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 743) = 3 ^ 9 * m + 3577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_743.1, data_12_743.2]

/-- Complete interval computation for depth 12, residue 744. -/
theorem bounds_12_744 : exactInterval 12 744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_744 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 744) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_744 : oddCount 744 12 = 3 ∧ acceleratedOrbit 12 744 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_744 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 744) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_744.1, data_12_744.2]

/-- Complete interval computation for depth 12, residue 745. -/
theorem bounds_12_745 : exactInterval 12 745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_745 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 745) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_745 : oddCount 745 12 = 9 ∧ acceleratedOrbit 12 745 = 3590 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_745 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 745) = 3 ^ 9 * m + 3590 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_745.1, data_12_745.2]

/-- Complete interval computation for depth 12, residue 746. -/
theorem bounds_12_746 : exactInterval 12 746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_746 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 746) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_746 : oddCount 746 12 = 3 ∧ acceleratedOrbit 12 746 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_746 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 746) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_746.1, data_12_746.2]

/-- Complete interval computation for depth 12, residue 747. -/
theorem bounds_12_747 : exactInterval 12 747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_747 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 747) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_747 : oddCount 747 12 = 7 ∧ acceleratedOrbit 12 747 = 400 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_747 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 747) = 3 ^ 7 * m + 400 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_747.1, data_12_747.2]

/-- Complete interval computation for depth 12, residue 748. -/
theorem bounds_12_748 : exactInterval 12 748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_748 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 748) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_748 : oddCount 748 12 = 7 ∧ acceleratedOrbit 12 748 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_748 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 748) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_748.1, data_12_748.2]

/-- Complete interval computation for depth 12, residue 749. -/
theorem bounds_12_749 : exactInterval 12 749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_749 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 749) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_749 : oddCount 749 12 = 7 ∧ acceleratedOrbit 12 749 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_749 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 749) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_749.1, data_12_749.2]

/-- Complete interval computation for depth 12, residue 750. -/
theorem bounds_12_750 : exactInterval 12 750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_750 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 750) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_750 : oddCount 750 12 = 7 ∧ acceleratedOrbit 12 750 = 404 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_750 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 750) = 3 ^ 7 * m + 404 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_750.1, data_12_750.2]

/-- Complete interval computation for depth 12, residue 751. -/
theorem bounds_12_751 : exactInterval 12 751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_751 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 751) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_751 : oddCount 751 12 = 10 ∧ acceleratedOrbit 12 751 = 10844 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_751 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 751) = 3 ^ 10 * m + 10844 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_751.1, data_12_751.2]

end Collatz.Research.StoppingAtlas.Batch0249
