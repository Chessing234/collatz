import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0515

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 727. -/
theorem bounds_13_727 : exactInterval 13 727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_727 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 727) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_727 : oddCount 727 13 = 6 ∧ acceleratedOrbit 13 727 = 65 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_727 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 727) = 3 ^ 6 * m + 65 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_727.1, data_13_727.2]

/-- Complete interval computation for depth 13, residue 728. -/
theorem bounds_13_728 : exactInterval 13 728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_728 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 728) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_728 : oddCount 728 13 = 8 ∧ acceleratedOrbit 13 728 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_728 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 728) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_728.1, data_13_728.2]

/-- Complete interval computation for depth 13, residue 729. -/
theorem bounds_13_729 : exactInterval 13 729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_729 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 729) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_729 : oddCount 729 13 = 5 ∧ acceleratedOrbit 13 729 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_729 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 729) = 3 ^ 5 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_729.1, data_13_729.2]

/-- Complete interval computation for depth 13, residue 730. -/
theorem bounds_13_730 : exactInterval 13 730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_730 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 730) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_730 : oddCount 730 13 = 8 ∧ acceleratedOrbit 13 730 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_730 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 730) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_730.1, data_13_730.2]

/-- Complete interval computation for depth 13, residue 731. -/
theorem bounds_13_731 : exactInterval 13 731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_731 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 731) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_731 : oddCount 731 13 = 8 ∧ acceleratedOrbit 13 731 = 587 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_731 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 731) = 3 ^ 8 * m + 587 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_731.1, data_13_731.2]

/-- Complete interval computation for depth 13, residue 732. -/
theorem bounds_13_732 : exactInterval 13 732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_732 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 732) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_732 : oddCount 732 13 = 8 ∧ acceleratedOrbit 13 732 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_732 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 732) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_732.1, data_13_732.2]

/-- Complete interval computation for depth 13, residue 733. -/
theorem bounds_13_733 : exactInterval 13 733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_733 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 733) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_733 : oddCount 733 13 = 8 ∧ acceleratedOrbit 13 733 = 593 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_733 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 733) = 3 ^ 8 * m + 593 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_733.1, data_13_733.2]

/-- Complete interval computation for depth 13, residue 734. -/
theorem bounds_13_734 : exactInterval 13 734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_734 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 734) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_734 : oddCount 734 13 = 7 ∧ acceleratedOrbit 13 734 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_734 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 734) = 3 ^ 7 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_734.1, data_13_734.2]

/-- Complete interval computation for depth 13, residue 735. -/
theorem bounds_13_735 : exactInterval 13 735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_735 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 735) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_735 : oddCount 735 13 = 7 ∧ acceleratedOrbit 13 735 = 197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_735 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 735) = 3 ^ 7 * m + 197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_735.1, data_13_735.2]

/-- Complete interval computation for depth 13, residue 736. -/
theorem bounds_13_736 : exactInterval 13 736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_736 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 736) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_736 : oddCount 736 13 = 4 ∧ acceleratedOrbit 13 736 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_736 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 736) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_736.1, data_13_736.2]

/-- Complete interval computation for depth 13, residue 737. -/
theorem bounds_13_737 : exactInterval 13 737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_737 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 737) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_737 : oddCount 737 13 = 9 ∧ acceleratedOrbit 13 737 = 1777 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_737 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 737) = 3 ^ 9 * m + 1777 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_737.1, data_13_737.2]

/-- Complete interval computation for depth 13, residue 738. -/
theorem bounds_13_738 : exactInterval 13 738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_738 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 738) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_738 : oddCount 738 13 = 4 ∧ acceleratedOrbit 13 738 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_738 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 738) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_738.1, data_13_738.2]

/-- Complete interval computation for depth 13, residue 739. -/
theorem bounds_13_739 : exactInterval 13 739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_739 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 739) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_739 : oddCount 739 13 = 4 ∧ acceleratedOrbit 13 739 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_739 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 739) = 3 ^ 4 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_739.1, data_13_739.2]

/-- Complete interval computation for depth 13, residue 740. -/
theorem bounds_13_740 : exactInterval 13 740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_740 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 740) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_740 : oddCount 740 13 = 6 ∧ acceleratedOrbit 13 740 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_740 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 740) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_740.1, data_13_740.2]

/-- Complete interval computation for depth 13, residue 741. -/
theorem bounds_13_741 : exactInterval 13 741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_741 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 741) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_741 : oddCount 741 13 = 6 ∧ acceleratedOrbit 13 741 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_741 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 741) = 3 ^ 6 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_741.1, data_13_741.2]

end Collatz.Research.StoppingAtlas.Batch0515
