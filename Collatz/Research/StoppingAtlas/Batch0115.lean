import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0115

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 727. -/
theorem bounds_11_727 : exactInterval 11 727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_727 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 727) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_727 : oddCount 727 11 = 6 ∧ acceleratedOrbit 11 727 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_727 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 727) = 3 ^ 6 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_727.1, data_11_727.2]

/-- Complete interval computation for depth 11, residue 728. -/
theorem bounds_11_728 : exactInterval 11 728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_728 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 728) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_728 : oddCount 728 11 = 6 ∧ acceleratedOrbit 11 728 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_728 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 728) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_728.1, data_11_728.2]

/-- Complete interval computation for depth 11, residue 729. -/
theorem bounds_11_729 : exactInterval 11 729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_729 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 729) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_729 : oddCount 729 11 = 4 ∧ acceleratedOrbit 11 729 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_729 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 729) = 3 ^ 4 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_729.1, data_11_729.2]

/-- Complete interval computation for depth 11, residue 730. -/
theorem bounds_11_730 : exactInterval 11 730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_730 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 730) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_730 : oddCount 730 11 = 6 ∧ acceleratedOrbit 11 730 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_730 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 730) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_730.1, data_11_730.2]

/-- Complete interval computation for depth 11, residue 731. -/
theorem bounds_11_731 : exactInterval 11 731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_731 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 731) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_731 : oddCount 731 11 = 8 ∧ acceleratedOrbit 11 731 = 2348 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_731 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 731) = 3 ^ 8 * m + 2348 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_731.1, data_11_731.2]

/-- Complete interval computation for depth 11, residue 732. -/
theorem bounds_11_732 : exactInterval 11 732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_732 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 732) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_732 : oddCount 732 11 = 6 ∧ acceleratedOrbit 11 732 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_732 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 732) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_732.1, data_11_732.2]

/-- Complete interval computation for depth 11, residue 733. -/
theorem bounds_11_733 : exactInterval 11 733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_733 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 733) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_733 : oddCount 733 11 = 6 ∧ acceleratedOrbit 11 733 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_733 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 733) = 3 ^ 6 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_733.1, data_11_733.2]

/-- Complete interval computation for depth 11, residue 734. -/
theorem bounds_11_734 : exactInterval 11 734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_734 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 734) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_734 : oddCount 734 11 = 6 ∧ acceleratedOrbit 11 734 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_734 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 734) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_734.1, data_11_734.2]

/-- Complete interval computation for depth 11, residue 735. -/
theorem bounds_11_735 : exactInterval 11 735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_735 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 735) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_735 : oddCount 735 11 = 6 ∧ acceleratedOrbit 11 735 = 262 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_735 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 735) = 3 ^ 6 * m + 262 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_735.1, data_11_735.2]

/-- Complete interval computation for depth 11, residue 736. -/
theorem bounds_11_736 : exactInterval 11 736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_736 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 736) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_736 : oddCount 736 11 = 3 ∧ acceleratedOrbit 11 736 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_736 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 736) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_736.1, data_11_736.2]

/-- Complete interval computation for depth 11, residue 737. -/
theorem bounds_11_737 : exactInterval 11 737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_737 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 737) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_737 : oddCount 737 11 = 8 ∧ acceleratedOrbit 11 737 = 2369 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_737 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 737) = 3 ^ 8 * m + 2369 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_737.1, data_11_737.2]

/-- Complete interval computation for depth 11, residue 738. -/
theorem bounds_11_738 : exactInterval 11 738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_738 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 738) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_738 : oddCount 738 11 = 3 ∧ acceleratedOrbit 11 738 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_738 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 738) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_738.1, data_11_738.2]

/-- Complete interval computation for depth 11, residue 739. -/
theorem bounds_11_739 : exactInterval 11 739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_739 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 739) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_739 : oddCount 739 11 = 3 ∧ acceleratedOrbit 11 739 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_739 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 739) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_739.1, data_11_739.2]

/-- Complete interval computation for depth 11, residue 740. -/
theorem bounds_11_740 : exactInterval 11 740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_740 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 740) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_740 : oddCount 740 11 = 5 ∧ acceleratedOrbit 11 740 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_740 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 740) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_740.1, data_11_740.2]

/-- Complete interval computation for depth 11, residue 741. -/
theorem bounds_11_741 : exactInterval 11 741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_741 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 741) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_741 : oddCount 741 11 = 5 ∧ acceleratedOrbit 11 741 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_741 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 741) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_741.1, data_11_741.2]

end Collatz.Research.StoppingAtlas.Batch0115
