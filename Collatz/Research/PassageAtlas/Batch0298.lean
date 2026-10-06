import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0298

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 9732. -/
theorem bounds_15_9732 : exactInterval 15 9732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9732 : oddCount 9732 15 = 6 ∧ acceleratedOrbit 15 9732 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9732) = 3 ^ 6 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9732.1, data_15_9732.2]

/-- Complete interval computation for depth 15, residue 9733. -/
theorem bounds_15_9733 : exactInterval 15 9733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9733 : oddCount 9733 15 = 6 ∧ acceleratedOrbit 15 9733 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9733) = 3 ^ 6 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9733.1, data_15_9733.2]

/-- Complete interval computation for depth 15, residue 9734. -/
theorem bounds_15_9734 : exactInterval 15 9734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9734 : oddCount 9734 15 = 6 ∧ acceleratedOrbit 15 9734 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9734) = 3 ^ 6 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9734.1, data_15_9734.2]

/-- Complete interval computation for depth 15, residue 9735. -/
theorem bounds_15_9735 : exactInterval 15 9735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9735 : oddCount 9735 15 = 7 ∧ acceleratedOrbit 15 9735 = 650 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9735) = 3 ^ 7 * m + 650 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9735.1, data_15_9735.2]

/-- Complete interval computation for depth 15, residue 9736. -/
theorem bounds_15_9736 : exactInterval 15 9736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9736 : oddCount 9736 15 = 6 ∧ acceleratedOrbit 15 9736 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9736) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9736.1, data_15_9736.2]

/-- Complete interval computation for depth 15, residue 9737. -/
theorem bounds_15_9737 : exactInterval 15 9737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9737 : oddCount 9737 15 = 9 ∧ acceleratedOrbit 15 9737 = 5852 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9737) = 3 ^ 9 * m + 5852 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9737.1, data_15_9737.2]

/-- Complete interval computation for depth 15, residue 9738. -/
theorem bounds_15_9738 : exactInterval 15 9738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9738 : oddCount 9738 15 = 6 ∧ acceleratedOrbit 15 9738 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9738) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9738.1, data_15_9738.2]

/-- Complete interval computation for depth 15, residue 9739. -/
theorem bounds_15_9739 : exactInterval 15 9739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9739 : oddCount 9739 15 = 6 ∧ acceleratedOrbit 15 9739 = 217 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9739) = 3 ^ 6 * m + 217 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9739.1, data_15_9739.2]

/-- Complete interval computation for depth 15, residue 9740. -/
theorem bounds_15_9740 : exactInterval 15 9740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9740 : oddCount 9740 15 = 6 ∧ acceleratedOrbit 15 9740 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9740) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9740.1, data_15_9740.2]

/-- Complete interval computation for depth 15, residue 9741. -/
theorem bounds_15_9741 : exactInterval 15 9741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9741 : oddCount 9741 15 = 6 ∧ acceleratedOrbit 15 9741 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9741) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9741.1, data_15_9741.2]

/-- Complete interval computation for depth 15, residue 9742. -/
theorem bounds_15_9742 : exactInterval 15 9742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9742 : oddCount 9742 15 = 8 ∧ acceleratedOrbit 15 9742 = 1952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9742) = 3 ^ 8 * m + 1952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9742.1, data_15_9742.2]

/-- Complete interval computation for depth 15, residue 9743. -/
theorem bounds_15_9743 : exactInterval 15 9743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9743 : oddCount 9743 15 = 8 ∧ acceleratedOrbit 15 9743 = 1952 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9743) = 3 ^ 8 * m + 1952 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9743.1, data_15_9743.2]

/-- Complete interval computation for depth 15, residue 9744. -/
theorem bounds_15_9744 : exactInterval 15 9744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9744 : oddCount 9744 15 = 6 ∧ acceleratedOrbit 15 9744 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9744) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9744.1, data_15_9744.2]

/-- Complete interval computation for depth 15, residue 9745. -/
theorem bounds_15_9745 : exactInterval 15 9745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9745 : oddCount 9745 15 = 6 ∧ acceleratedOrbit 15 9745 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9745) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9745.1, data_15_9745.2]

/-- Complete interval computation for depth 15, residue 9746. -/
theorem bounds_15_9746 : exactInterval 15 9746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9746 : oddCount 9746 15 = 9 ∧ acceleratedOrbit 15 9746 = 5858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9746) = 3 ^ 9 * m + 5858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9746.1, data_15_9746.2]

/-- Complete interval computation for depth 15, residue 9747. -/
theorem bounds_15_9747 : exactInterval 15 9747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9747 : oddCount 9747 15 = 9 ∧ acceleratedOrbit 15 9747 = 5858 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9747) = 3 ^ 9 * m + 5858 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9747.1, data_15_9747.2]

/-- Complete interval computation for depth 15, residue 9748. -/
theorem bounds_15_9748 : exactInterval 15 9748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9748 : oddCount 9748 15 = 6 ∧ acceleratedOrbit 15 9748 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9748) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9748.1, data_15_9748.2]

/-- Complete interval computation for depth 15, residue 9749. -/
theorem bounds_15_9749 : exactInterval 15 9749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9749 : oddCount 9749 15 = 6 ∧ acceleratedOrbit 15 9749 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9749) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9749.1, data_15_9749.2]

/-- Complete interval computation for depth 15, residue 9750. -/
theorem bounds_15_9750 : exactInterval 15 9750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9750 : oddCount 9750 15 = 8 ∧ acceleratedOrbit 15 9750 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9750) = 3 ^ 8 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9750.1, data_15_9750.2]

/-- Complete interval computation for depth 15, residue 9751. -/
theorem bounds_15_9751 : exactInterval 15 9751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9751 : oddCount 9751 15 = 8 ∧ acceleratedOrbit 15 9751 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9751) = 3 ^ 8 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9751.1, data_15_9751.2]

/-- Complete interval computation for depth 15, residue 9752. -/
theorem bounds_15_9752 : exactInterval 15 9752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9752 : oddCount 9752 15 = 6 ∧ acceleratedOrbit 15 9752 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9752) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9752.1, data_15_9752.2]

/-- Complete interval computation for depth 15, residue 9753. -/
theorem bounds_15_9753 : exactInterval 15 9753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9753 : oddCount 9753 15 = 8 ∧ acceleratedOrbit 15 9753 = 1954 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9753) = 3 ^ 8 * m + 1954 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9753.1, data_15_9753.2]

/-- Complete interval computation for depth 15, residue 9754. -/
theorem bounds_15_9754 : exactInterval 15 9754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9754 : oddCount 9754 15 = 6 ∧ acceleratedOrbit 15 9754 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9754) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9754.1, data_15_9754.2]

/-- Complete interval computation for depth 15, residue 9755. -/
theorem bounds_15_9755 : exactInterval 15 9755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9755 : oddCount 9755 15 = 9 ∧ acceleratedOrbit 15 9755 = 5861 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9755) = 3 ^ 9 * m + 5861 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9755.1, data_15_9755.2]

/-- Complete interval computation for depth 15, residue 9756. -/
theorem bounds_15_9756 : exactInterval 15 9756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9756 : oddCount 9756 15 = 6 ∧ acceleratedOrbit 15 9756 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9756) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9756.1, data_15_9756.2]

/-- Complete interval computation for depth 15, residue 9757. -/
theorem bounds_15_9757 : exactInterval 15 9757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9757 : oddCount 9757 15 = 6 ∧ acceleratedOrbit 15 9757 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9757) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9757.1, data_15_9757.2]

/-- Complete interval computation for depth 15, residue 9758. -/
theorem bounds_15_9758 : exactInterval 15 9758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9758 : oddCount 9758 15 = 6 ∧ acceleratedOrbit 15 9758 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9758) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9758.1, data_15_9758.2]

/-- Complete interval computation for depth 15, residue 9759. -/
theorem bounds_15_9759 : exactInterval 15 9759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9759 : oddCount 9759 15 = 9 ∧ acceleratedOrbit 15 9759 = 5863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9759) = 3 ^ 9 * m + 5863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9759.1, data_15_9759.2]

/-- Complete interval computation for depth 15, residue 9760. -/
theorem bounds_15_9760 : exactInterval 15 9760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9760 : oddCount 9760 15 = 5 ∧ acceleratedOrbit 15 9760 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9760) = 3 ^ 5 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9760.1, data_15_9760.2]

/-- Complete interval computation for depth 15, residue 9761. -/
theorem bounds_15_9761 : exactInterval 15 9761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9761 : oddCount 9761 15 = 7 ∧ acceleratedOrbit 15 9761 = 652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9761) = 3 ^ 7 * m + 652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9761.1, data_15_9761.2]

/-- Complete interval computation for depth 15, residue 9762. -/
theorem bounds_15_9762 : exactInterval 15 9762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9762 : oddCount 9762 15 = 6 ∧ acceleratedOrbit 15 9762 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9762) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9762.1, data_15_9762.2]

/-- Complete interval computation for depth 15, residue 9763. -/
theorem bounds_15_9763 : exactInterval 15 9763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_9763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 9763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_9763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_9763 : oddCount 9763 15 = 6 ∧ acceleratedOrbit 15 9763 = 218 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_9763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 9763) = 3 ^ 6 * m + 218 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_9763.1, data_15_9763.2]

end Collatz.Research.PassageAtlas.Batch0298
