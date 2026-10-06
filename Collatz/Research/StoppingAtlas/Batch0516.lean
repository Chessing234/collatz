import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0516

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 742. -/
theorem bounds_13_742 : exactInterval 13 742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_742 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 742) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_742 : oddCount 742 13 = 6 ∧ acceleratedOrbit 13 742 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_742 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 742) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_742.1, data_13_742.2]

/-- Complete interval computation for depth 13, residue 743. -/
theorem bounds_13_743 : exactInterval 13 743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_743 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 743) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_743 : oddCount 743 13 = 10 ∧ acceleratedOrbit 13 743 = 5366 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_743 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 743) = 3 ^ 10 * m + 5366 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_743.1, data_13_743.2]

/-- Complete interval computation for depth 13, residue 744. -/
theorem bounds_13_744 : exactInterval 13 744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_744 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 744) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_744 : oddCount 744 13 = 4 ∧ acceleratedOrbit 13 744 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_744 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 744) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_744.1, data_13_744.2]

/-- Complete interval computation for depth 13, residue 745. -/
theorem bounds_13_745 : exactInterval 13 745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_745 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 745) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_745 : oddCount 745 13 = 9 ∧ acceleratedOrbit 13 745 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_745 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 745) = 3 ^ 9 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_745.1, data_13_745.2]

/-- Complete interval computation for depth 13, residue 746. -/
theorem bounds_13_746 : exactInterval 13 746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_746 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 746) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_746 : oddCount 746 13 = 4 ∧ acceleratedOrbit 13 746 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_746 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 746) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_746.1, data_13_746.2]

/-- Complete interval computation for depth 13, residue 747. -/
theorem bounds_13_747 : exactInterval 13 747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_747 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 747) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_747 : oddCount 747 13 = 7 ∧ acceleratedOrbit 13 747 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_747 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 747) = 3 ^ 7 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_747.1, data_13_747.2]

/-- Complete interval computation for depth 13, residue 748. -/
theorem bounds_13_748 : exactInterval 13 748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_748 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 748) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_748 : oddCount 748 13 = 7 ∧ acceleratedOrbit 13 748 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_748 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 748) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_748.1, data_13_748.2]

/-- Complete interval computation for depth 13, residue 749. -/
theorem bounds_13_749 : exactInterval 13 749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_749 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 749) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_749 : oddCount 749 13 = 7 ∧ acceleratedOrbit 13 749 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_749 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 749) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_749.1, data_13_749.2]

/-- Complete interval computation for depth 13, residue 750. -/
theorem bounds_13_750 : exactInterval 13 750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_750 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 750) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_750 : oddCount 750 13 = 7 ∧ acceleratedOrbit 13 750 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_750 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 750) = 3 ^ 7 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_750.1, data_13_750.2]

/-- Complete interval computation for depth 13, residue 751. -/
theorem bounds_13_751 : exactInterval 13 751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_751 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 751) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_751 : oddCount 751 13 = 10 ∧ acceleratedOrbit 13 751 = 5422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_751 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 751) = 3 ^ 10 * m + 5422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_751.1, data_13_751.2]

/-- Complete interval computation for depth 13, residue 752. -/
theorem bounds_13_752 : exactInterval 13 752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_752 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 752) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_752 : oddCount 752 13 = 7 ∧ acceleratedOrbit 13 752 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_752 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 752) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_752.1, data_13_752.2]

/-- Complete interval computation for depth 13, residue 753. -/
theorem bounds_13_753 : exactInterval 13 753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_753 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 753) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_753 : oddCount 753 13 = 4 ∧ acceleratedOrbit 13 753 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_753 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 753) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_753.1, data_13_753.2]

/-- Complete interval computation for depth 13, residue 754. -/
theorem bounds_13_754 : exactInterval 13 754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_754 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 754) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_754 : oddCount 754 13 = 9 ∧ acceleratedOrbit 13 754 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_754 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 754) = 3 ^ 9 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_754.1, data_13_754.2]

/-- Complete interval computation for depth 13, residue 755. -/
theorem bounds_13_755 : exactInterval 13 755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_755 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 755) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_755 : oddCount 755 13 = 9 ∧ acceleratedOrbit 13 755 = 1822 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_755 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 755) = 3 ^ 9 * m + 1822 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_755.1, data_13_755.2]

/-- Complete interval computation for depth 13, residue 756. -/
theorem bounds_13_756 : exactInterval 13 756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_756 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 756) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_756 : oddCount 756 13 = 7 ∧ acceleratedOrbit 13 756 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_756 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 756) = 3 ^ 7 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_756.1, data_13_756.2]

end Collatz.Research.StoppingAtlas.Batch0516
