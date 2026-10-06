import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0420

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 13729. -/
theorem bounds_15_13729 : exactInterval 15 13729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13729 : oddCount 13729 15 = 7 ∧ acceleratedOrbit 15 13729 = 917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13729) = 3 ^ 7 * m + 917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13729.1, data_15_13729.2]

/-- Complete interval computation for depth 15, residue 13730. -/
theorem bounds_15_13730 : exactInterval 15 13730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13730 : oddCount 13730 15 = 8 ∧ acceleratedOrbit 15 13730 = 2753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13730) = 3 ^ 8 * m + 2753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13730.1, data_15_13730.2]

/-- Complete interval computation for depth 15, residue 13731. -/
theorem bounds_15_13731 : exactInterval 15 13731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13731 : oddCount 13731 15 = 8 ∧ acceleratedOrbit 15 13731 = 2753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13731) = 3 ^ 8 * m + 2753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13731.1, data_15_13731.2]

/-- Complete interval computation for depth 15, residue 13732. -/
theorem bounds_15_13732 : exactInterval 15 13732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13732 : oddCount 13732 15 = 8 ∧ acceleratedOrbit 15 13732 = 2753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13732) = 3 ^ 8 * m + 2753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13732.1, data_15_13732.2]

/-- Complete interval computation for depth 15, residue 13733. -/
theorem bounds_15_13733 : exactInterval 15 13733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13733 : oddCount 13733 15 = 8 ∧ acceleratedOrbit 15 13733 = 2753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13733) = 3 ^ 8 * m + 2753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13733.1, data_15_13733.2]

/-- Complete interval computation for depth 15, residue 13734. -/
theorem bounds_15_13734 : exactInterval 15 13734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13734 : oddCount 13734 15 = 8 ∧ acceleratedOrbit 15 13734 = 2753 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13734) = 3 ^ 8 * m + 2753 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13734.1, data_15_13734.2]

/-- Complete interval computation for depth 15, residue 13735. -/
theorem bounds_15_13735 : exactInterval 15 13735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13735 : oddCount 13735 15 = 9 ∧ acceleratedOrbit 15 13735 = 8252 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13735) = 3 ^ 9 * m + 8252 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13735.1, data_15_13735.2]

/-- Complete interval computation for depth 15, residue 13736. -/
theorem bounds_15_13736 : exactInterval 15 13736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13736 : oddCount 13736 15 = 5 ∧ acceleratedOrbit 15 13736 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13736) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13736.1, data_15_13736.2]

/-- Complete interval computation for depth 15, residue 13737. -/
theorem bounds_15_13737 : exactInterval 15 13737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13737 : oddCount 13737 15 = 11 ∧ acceleratedOrbit 15 13737 = 74276 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13737) = 3 ^ 11 * m + 74276 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13737.1, data_15_13737.2]

/-- Complete interval computation for depth 15, residue 13738. -/
theorem bounds_15_13738 : exactInterval 15 13738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13738 : oddCount 13738 15 = 5 ∧ acceleratedOrbit 15 13738 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13738) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13738.1, data_15_13738.2]

/-- Complete interval computation for depth 15, residue 13739. -/
theorem bounds_15_13739 : exactInterval 15 13739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13739 : oddCount 13739 15 = 9 ∧ acceleratedOrbit 15 13739 = 8255 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13739) = 3 ^ 9 * m + 8255 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13739.1, data_15_13739.2]

/-- Complete interval computation for depth 15, residue 13740. -/
theorem bounds_15_13740 : exactInterval 15 13740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13740 : oddCount 13740 15 = 9 ∧ acceleratedOrbit 15 13740 = 8261 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13740) = 3 ^ 9 * m + 8261 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13740.1, data_15_13740.2]

/-- Complete interval computation for depth 15, residue 13741. -/
theorem bounds_15_13741 : exactInterval 15 13741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13741 : oddCount 13741 15 = 9 ∧ acceleratedOrbit 15 13741 = 8261 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13741) = 3 ^ 9 * m + 8261 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13741.1, data_15_13741.2]

/-- Complete interval computation for depth 15, residue 13742. -/
theorem bounds_15_13742 : exactInterval 15 13742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13742 : oddCount 13742 15 = 9 ∧ acceleratedOrbit 15 13742 = 8261 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13742) = 3 ^ 9 * m + 8261 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13742.1, data_15_13742.2]

/-- Complete interval computation for depth 15, residue 13743. -/
theorem bounds_15_13743 : exactInterval 15 13743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13743 : oddCount 13743 15 = 9 ∧ acceleratedOrbit 15 13743 = 8257 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13743) = 3 ^ 9 * m + 8257 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13743.1, data_15_13743.2]

/-- Complete interval computation for depth 15, residue 13744. -/
theorem bounds_15_13744 : exactInterval 15 13744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13744 : oddCount 13744 15 = 7 ∧ acceleratedOrbit 15 13744 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13744) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13744.1, data_15_13744.2]

/-- Complete interval computation for depth 15, residue 13745. -/
theorem bounds_15_13745 : exactInterval 15 13745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13745 : oddCount 13745 15 = 4 ∧ acceleratedOrbit 15 13745 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13745) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13745.1, data_15_13745.2]

/-- Complete interval computation for depth 15, residue 13746. -/
theorem bounds_15_13746 : exactInterval 15 13746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13746 : oddCount 13746 15 = 4 ∧ acceleratedOrbit 15 13746 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13746) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13746.1, data_15_13746.2]

/-- Complete interval computation for depth 15, residue 13747. -/
theorem bounds_15_13747 : exactInterval 15 13747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13747 : oddCount 13747 15 = 4 ∧ acceleratedOrbit 15 13747 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13747) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13747.1, data_15_13747.2]

/-- Complete interval computation for depth 15, residue 13748. -/
theorem bounds_15_13748 : exactInterval 15 13748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13748 : oddCount 13748 15 = 7 ∧ acceleratedOrbit 15 13748 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13748) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13748.1, data_15_13748.2]

/-- Complete interval computation for depth 15, residue 13749. -/
theorem bounds_15_13749 : exactInterval 15 13749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13749 : oddCount 13749 15 = 7 ∧ acceleratedOrbit 15 13749 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13749) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13749.1, data_15_13749.2]

/-- Complete interval computation for depth 15, residue 13750. -/
theorem bounds_15_13750 : exactInterval 15 13750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13750 : oddCount 13750 15 = 11 ∧ acceleratedOrbit 15 13750 = 74357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13750) = 3 ^ 11 * m + 74357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13750.1, data_15_13750.2]

/-- Complete interval computation for depth 15, residue 13751. -/
theorem bounds_15_13751 : exactInterval 15 13751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13751 : oddCount 13751 15 = 11 ∧ acceleratedOrbit 15 13751 = 74357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13751) = 3 ^ 11 * m + 74357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13751.1, data_15_13751.2]

/-- Complete interval computation for depth 15, residue 13752. -/
theorem bounds_15_13752 : exactInterval 15 13752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13752 : oddCount 13752 15 = 7 ∧ acceleratedOrbit 15 13752 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13752) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13752.1, data_15_13752.2]

/-- Complete interval computation for depth 15, residue 13753. -/
theorem bounds_15_13753 : exactInterval 15 13753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13753 : oddCount 13753 15 = 4 ∧ acceleratedOrbit 15 13753 = 34 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13753) = 3 ^ 4 * m + 34 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13753.1, data_15_13753.2]

/-- Complete interval computation for depth 15, residue 13754. -/
theorem bounds_15_13754 : exactInterval 15 13754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13754 : oddCount 13754 15 = 7 ∧ acceleratedOrbit 15 13754 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13754) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13754.1, data_15_13754.2]

/-- Complete interval computation for depth 15, residue 13755. -/
theorem bounds_15_13755 : exactInterval 15 13755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13755 : oddCount 13755 15 = 8 ∧ acceleratedOrbit 15 13755 = 2755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13755) = 3 ^ 8 * m + 2755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13755.1, data_15_13755.2]

/-- Complete interval computation for depth 15, residue 13756. -/
theorem bounds_15_13756 : exactInterval 15 13756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13756 : oddCount 13756 15 = 8 ∧ acceleratedOrbit 15 13756 = 2756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13756) = 3 ^ 8 * m + 2756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13756.1, data_15_13756.2]

/-- Complete interval computation for depth 15, residue 13757. -/
theorem bounds_15_13757 : exactInterval 15 13757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13757 : oddCount 13757 15 = 8 ∧ acceleratedOrbit 15 13757 = 2756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13757) = 3 ^ 8 * m + 2756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13757.1, data_15_13757.2]

/-- Complete interval computation for depth 15, residue 13758. -/
theorem bounds_15_13758 : exactInterval 15 13758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13758 : oddCount 13758 15 = 8 ∧ acceleratedOrbit 15 13758 = 2756 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13758) = 3 ^ 8 * m + 2756 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13758.1, data_15_13758.2]

/-- Complete interval computation for depth 15, residue 13759. -/
theorem bounds_15_13759 : exactInterval 15 13759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13759 : oddCount 13759 15 = 12 ∧ acceleratedOrbit 15 13759 = 223165 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13759) = 3 ^ 12 * m + 223165 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13759.1, data_15_13759.2]

/-- Complete interval computation for depth 15, residue 13760. -/
theorem bounds_15_13760 : exactInterval 15 13760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13760 : oddCount 13760 15 = 5 ∧ acceleratedOrbit 15 13760 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13760) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13760.1, data_15_13760.2]

/-- Complete interval computation for depth 15, residue 13761. -/
theorem bounds_15_13761 : exactInterval 15 13761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_13761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 13761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_13761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_13761 : oddCount 13761 15 = 7 ∧ acceleratedOrbit 15 13761 = 919 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_13761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 13761) = 3 ^ 7 * m + 919 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_13761.1, data_15_13761.2]

end Collatz.Research.PassageAtlas.Batch0420
