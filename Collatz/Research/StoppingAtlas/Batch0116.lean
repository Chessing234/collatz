import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0116

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 742. -/
theorem bounds_11_742 : exactInterval 11 742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_742 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 742) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_742 : oddCount 742 11 = 5 ∧ acceleratedOrbit 11 742 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_742 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 742) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_742.1, data_11_742.2]

/-- Complete interval computation for depth 11, residue 743. -/
theorem bounds_11_743 : exactInterval 11 743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_743 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 743) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_743 : oddCount 743 11 = 9 ∧ acceleratedOrbit 11 743 = 7154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_743 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 743) = 3 ^ 9 * m + 7154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_743.1, data_11_743.2]

/-- Complete interval computation for depth 11, residue 744. -/
theorem bounds_11_744 : exactInterval 11 744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_744 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 744) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_744 : oddCount 744 11 = 3 ∧ acceleratedOrbit 11 744 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_744 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 744) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_744.1, data_11_744.2]

/-- Complete interval computation for depth 11, residue 745. -/
theorem bounds_11_745 : exactInterval 11 745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_745 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 745) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_745 : oddCount 745 11 = 8 ∧ acceleratedOrbit 11 745 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_745 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 745) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_745.1, data_11_745.2]

/-- Complete interval computation for depth 11, residue 746. -/
theorem bounds_11_746 : exactInterval 11 746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_746 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 746) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_746 : oddCount 746 11 = 3 ∧ acceleratedOrbit 11 746 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_746 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 746) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_746.1, data_11_746.2]

/-- Complete interval computation for depth 11, residue 747. -/
theorem bounds_11_747 : exactInterval 11 747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_747 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 747) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_747 : oddCount 747 11 = 7 ∧ acceleratedOrbit 11 747 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_747 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 747) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_747.1, data_11_747.2]

/-- Complete interval computation for depth 11, residue 748. -/
theorem bounds_11_748 : exactInterval 11 748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_748 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 748) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_748 : oddCount 748 11 = 6 ∧ acceleratedOrbit 11 748 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_748 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 748) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_748.1, data_11_748.2]

/-- Complete interval computation for depth 11, residue 749. -/
theorem bounds_11_749 : exactInterval 11 749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_749 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 749) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_749 : oddCount 749 11 = 6 ∧ acceleratedOrbit 11 749 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_749 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 749) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_749.1, data_11_749.2]

/-- Complete interval computation for depth 11, residue 750. -/
theorem bounds_11_750 : exactInterval 11 750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_750 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 750) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_750 : oddCount 750 11 = 6 ∧ acceleratedOrbit 11 750 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_750 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 750) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_750.1, data_11_750.2]

/-- Complete interval computation for depth 11, residue 751. -/
theorem bounds_11_751 : exactInterval 11 751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_751 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 751) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_751 : oddCount 751 11 = 9 ∧ acceleratedOrbit 11 751 = 7229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_751 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 751) = 3 ^ 9 * m + 7229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_751.1, data_11_751.2]

/-- Complete interval computation for depth 11, residue 752. -/
theorem bounds_11_752 : exactInterval 11 752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_752 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 752) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_752 : oddCount 752 11 = 5 ∧ acceleratedOrbit 11 752 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_752 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 752) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_752.1, data_11_752.2]

/-- Complete interval computation for depth 11, residue 753. -/
theorem bounds_11_753 : exactInterval 11 753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_753 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 753) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_753 : oddCount 753 11 = 3 ∧ acceleratedOrbit 11 753 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_753 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 753) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_753.1, data_11_753.2]

/-- Complete interval computation for depth 11, residue 754. -/
theorem bounds_11_754 : exactInterval 11 754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_754 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 754) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_754 : oddCount 754 11 = 8 ∧ acceleratedOrbit 11 754 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_754 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 754) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_754.1, data_11_754.2]

/-- Complete interval computation for depth 11, residue 755. -/
theorem bounds_11_755 : exactInterval 11 755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_755 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 755) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_755 : oddCount 755 11 = 8 ∧ acceleratedOrbit 11 755 = 2429 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_755 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 755) = 3 ^ 8 * m + 2429 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_755.1, data_11_755.2]

/-- Complete interval computation for depth 11, residue 756. -/
theorem bounds_11_756 : exactInterval 11 756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_756 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 756) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_756 : oddCount 756 11 = 5 ∧ acceleratedOrbit 11 756 = 91 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_756 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 756) = 3 ^ 5 * m + 91 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_756.1, data_11_756.2]

end Collatz.Research.StoppingAtlas.Batch0116
