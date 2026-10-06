import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0756

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24739. -/
theorem bounds_15_24739 : exactInterval 15 24739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24739 : oddCount 24739 15 = 6 ∧ acceleratedOrbit 15 24739 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24739) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24739.1, data_15_24739.2]

/-- Complete interval computation for depth 15, residue 24740. -/
theorem bounds_15_24740 : exactInterval 15 24740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24740 : oddCount 24740 15 = 8 ∧ acceleratedOrbit 15 24740 = 4955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24740) = 3 ^ 8 * m + 4955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24740.1, data_15_24740.2]

/-- Complete interval computation for depth 15, residue 24741. -/
theorem bounds_15_24741 : exactInterval 15 24741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24741 : oddCount 24741 15 = 8 ∧ acceleratedOrbit 15 24741 = 4955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24741) = 3 ^ 8 * m + 4955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24741.1, data_15_24741.2]

/-- Complete interval computation for depth 15, residue 24742. -/
theorem bounds_15_24742 : exactInterval 15 24742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24742 : oddCount 24742 15 = 8 ∧ acceleratedOrbit 15 24742 = 4955 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24742) = 3 ^ 8 * m + 4955 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24742.1, data_15_24742.2]

/-- Complete interval computation for depth 15, residue 24743. -/
theorem bounds_15_24743 : exactInterval 15 24743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24743 : oddCount 24743 15 = 12 ∧ acceleratedOrbit 15 24743 = 401314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24743) = 3 ^ 12 * m + 401314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24743.1, data_15_24743.2]

/-- Complete interval computation for depth 15, residue 24744. -/
theorem bounds_15_24744 : exactInterval 15 24744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24744 : oddCount 24744 15 = 4 ∧ acceleratedOrbit 15 24744 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24744) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24744.1, data_15_24744.2]

/-- Complete interval computation for depth 15, residue 24745. -/
theorem bounds_15_24745 : exactInterval 15 24745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24745 : oddCount 24745 15 = 11 ∧ acceleratedOrbit 15 24745 = 133784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24745) = 3 ^ 11 * m + 133784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24745.1, data_15_24745.2]

/-- Complete interval computation for depth 15, residue 24746. -/
theorem bounds_15_24746 : exactInterval 15 24746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24746 : oddCount 24746 15 = 4 ∧ acceleratedOrbit 15 24746 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24746) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24746.1, data_15_24746.2]

/-- Complete interval computation for depth 15, residue 24747. -/
theorem bounds_15_24747 : exactInterval 15 24747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24747 : oddCount 24747 15 = 7 ∧ acceleratedOrbit 15 24747 = 1652 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24747) = 3 ^ 7 * m + 1652 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24747.1, data_15_24747.2]

/-- Complete interval computation for depth 15, residue 24748. -/
theorem bounds_15_24748 : exactInterval 15 24748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24748 : oddCount 24748 15 = 6 ∧ acceleratedOrbit 15 24748 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24748) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24748.1, data_15_24748.2]

/-- Complete interval computation for depth 15, residue 24749. -/
theorem bounds_15_24749 : exactInterval 15 24749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24749 : oddCount 24749 15 = 6 ∧ acceleratedOrbit 15 24749 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24749) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24749.1, data_15_24749.2]

/-- Complete interval computation for depth 15, residue 24750. -/
theorem bounds_15_24750 : exactInterval 15 24750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24750 : oddCount 24750 15 = 6 ∧ acceleratedOrbit 15 24750 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24750) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24750.1, data_15_24750.2]

/-- Complete interval computation for depth 15, residue 24751. -/
theorem bounds_15_24751 : exactInterval 15 24751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24751 : oddCount 24751 15 = 10 ∧ acceleratedOrbit 15 24751 = 44606 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24751) = 3 ^ 10 * m + 44606 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24751.1, data_15_24751.2]

/-- Complete interval computation for depth 15, residue 24752. -/
theorem bounds_15_24752 : exactInterval 15 24752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24752 : oddCount 24752 15 = 5 ∧ acceleratedOrbit 15 24752 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24752) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24752.1, data_15_24752.2]

/-- Complete interval computation for depth 15, residue 24753. -/
theorem bounds_15_24753 : exactInterval 15 24753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24753 : oddCount 24753 15 = 6 ∧ acceleratedOrbit 15 24753 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24753) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24753.1, data_15_24753.2]

/-- Complete interval computation for depth 15, residue 24754. -/
theorem bounds_15_24754 : exactInterval 15 24754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24754 : oddCount 24754 15 = 6 ∧ acceleratedOrbit 15 24754 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24754) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24754.1, data_15_24754.2]

/-- Complete interval computation for depth 15, residue 24755. -/
theorem bounds_15_24755 : exactInterval 15 24755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24755 : oddCount 24755 15 = 6 ∧ acceleratedOrbit 15 24755 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24755) = 3 ^ 6 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24755.1, data_15_24755.2]

/-- Complete interval computation for depth 15, residue 24756. -/
theorem bounds_15_24756 : exactInterval 15 24756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24756 : oddCount 24756 15 = 5 ∧ acceleratedOrbit 15 24756 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24756) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24756.1, data_15_24756.2]

/-- Complete interval computation for depth 15, residue 24757. -/
theorem bounds_15_24757 : exactInterval 15 24757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24757 : oddCount 24757 15 = 5 ∧ acceleratedOrbit 15 24757 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24757) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24757.1, data_15_24757.2]

/-- Complete interval computation for depth 15, residue 24758. -/
theorem bounds_15_24758 : exactInterval 15 24758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24758 : oddCount 24758 15 = 10 ∧ acceleratedOrbit 15 24758 = 44621 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24758) = 3 ^ 10 * m + 44621 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24758.1, data_15_24758.2]

/-- Complete interval computation for depth 15, residue 24759. -/
theorem bounds_15_24759 : exactInterval 15 24759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24759 : oddCount 24759 15 = 10 ∧ acceleratedOrbit 15 24759 = 44621 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24759) = 3 ^ 10 * m + 44621 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24759.1, data_15_24759.2]

/-- Complete interval computation for depth 15, residue 24760. -/
theorem bounds_15_24760 : exactInterval 15 24760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24760 : oddCount 24760 15 = 5 ∧ acceleratedOrbit 15 24760 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24760) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24760.1, data_15_24760.2]

/-- Complete interval computation for depth 15, residue 24761. -/
theorem bounds_15_24761 : exactInterval 15 24761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24761 : oddCount 24761 15 = 10 ∧ acceleratedOrbit 15 24761 = 44630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24761) = 3 ^ 10 * m + 44630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24761.1, data_15_24761.2]

/-- Complete interval computation for depth 15, residue 24762. -/
theorem bounds_15_24762 : exactInterval 15 24762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24762 : oddCount 24762 15 = 5 ∧ acceleratedOrbit 15 24762 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24762) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24762.1, data_15_24762.2]

/-- Complete interval computation for depth 15, residue 24763. -/
theorem bounds_15_24763 : exactInterval 15 24763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24763 : oddCount 24763 15 = 10 ∧ acceleratedOrbit 15 24763 = 44630 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24763) = 3 ^ 10 * m + 44630 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24763.1, data_15_24763.2]

/-- Complete interval computation for depth 15, residue 24764. -/
theorem bounds_15_24764 : exactInterval 15 24764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24764 : oddCount 24764 15 = 9 ∧ acceleratedOrbit 15 24764 = 14879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24764) = 3 ^ 9 * m + 14879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24764.1, data_15_24764.2]

/-- Complete interval computation for depth 15, residue 24765. -/
theorem bounds_15_24765 : exactInterval 15 24765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24765 : oddCount 24765 15 = 9 ∧ acceleratedOrbit 15 24765 = 14879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24765) = 3 ^ 9 * m + 14879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24765.1, data_15_24765.2]

/-- Complete interval computation for depth 15, residue 24766. -/
theorem bounds_15_24766 : exactInterval 15 24766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24766 : oddCount 24766 15 = 9 ∧ acceleratedOrbit 15 24766 = 14879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24766) = 3 ^ 9 * m + 14879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24766.1, data_15_24766.2]

/-- Complete interval computation for depth 15, residue 24767. -/
theorem bounds_15_24767 : exactInterval 15 24767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24767 : oddCount 24767 15 = 9 ∧ acceleratedOrbit 15 24767 = 14878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24767) = 3 ^ 9 * m + 14878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24767.1, data_15_24767.2]

/-- Complete interval computation for depth 15, residue 24768. -/
theorem bounds_15_24768 : exactInterval 15 24768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24768 : oddCount 24768 15 = 4 ∧ acceleratedOrbit 15 24768 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24768) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24768.1, data_15_24768.2]

/-- Complete interval computation for depth 15, residue 24769. -/
theorem bounds_15_24769 : exactInterval 15 24769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24769 : oddCount 24769 15 = 8 ∧ acceleratedOrbit 15 24769 = 4961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24769) = 3 ^ 8 * m + 4961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24769.1, data_15_24769.2]

/-- Complete interval computation for depth 15, residue 24770. -/
theorem bounds_15_24770 : exactInterval 15 24770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24770 : oddCount 24770 15 = 8 ∧ acceleratedOrbit 15 24770 = 4961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24770) = 3 ^ 8 * m + 4961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24770.1, data_15_24770.2]

/-- Complete interval computation for depth 15, residue 24771. -/
theorem bounds_15_24771 : exactInterval 15 24771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24771 : oddCount 24771 15 = 8 ∧ acceleratedOrbit 15 24771 = 4961 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24771) = 3 ^ 8 * m + 4961 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24771.1, data_15_24771.2]

end Collatz.Research.PassageAtlas.Batch0756
