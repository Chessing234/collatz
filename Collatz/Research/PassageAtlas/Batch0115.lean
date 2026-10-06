import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0115

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3735. -/
theorem bounds_15_3735 : exactInterval 15 3735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3735 : oddCount 3735 15 = 5 ∧ acceleratedOrbit 15 3735 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3735) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3735.1, data_15_3735.2]

/-- Complete interval computation for depth 15, residue 3736. -/
theorem bounds_15_3736 : exactInterval 15 3736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3736 : oddCount 3736 15 = 7 ∧ acceleratedOrbit 15 3736 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3736) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3736.1, data_15_3736.2]

/-- Complete interval computation for depth 15, residue 3737. -/
theorem bounds_15_3737 : exactInterval 15 3737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3737 : oddCount 3737 15 = 10 ∧ acceleratedOrbit 15 3737 = 6743 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3737) = 3 ^ 10 * m + 6743 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3737.1, data_15_3737.2]

/-- Complete interval computation for depth 15, residue 3738. -/
theorem bounds_15_3738 : exactInterval 15 3738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3738 : oddCount 3738 15 = 7 ∧ acceleratedOrbit 15 3738 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3738) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3738.1, data_15_3738.2]

/-- Complete interval computation for depth 15, residue 3739. -/
theorem bounds_15_3739 : exactInterval 15 3739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3739 : oddCount 3739 15 = 12 ∧ acceleratedOrbit 15 3739 = 60668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3739) = 3 ^ 12 * m + 60668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3739.1, data_15_3739.2]

/-- Complete interval computation for depth 15, residue 3740. -/
theorem bounds_15_3740 : exactInterval 15 3740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3740 : oddCount 3740 15 = 7 ∧ acceleratedOrbit 15 3740 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3740) = 3 ^ 7 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3740.1, data_15_3740.2]

/-- Complete interval computation for depth 15, residue 3741. -/
theorem bounds_15_3741 : exactInterval 15 3741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3741 : oddCount 3741 15 = 7 ∧ acceleratedOrbit 15 3741 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3741) = 3 ^ 7 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3741.1, data_15_3741.2]

/-- Complete interval computation for depth 15, residue 3742. -/
theorem bounds_15_3742 : exactInterval 15 3742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3742 : oddCount 3742 15 = 7 ∧ acceleratedOrbit 15 3742 = 250 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3742) = 3 ^ 7 * m + 250 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3742.1, data_15_3742.2]

/-- Complete interval computation for depth 15, residue 3743. -/
theorem bounds_15_3743 : exactInterval 15 3743 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3743) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3743 : oddCount 3743 15 = 9 ∧ acceleratedOrbit 15 3743 = 2249 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3743) = 3 ^ 9 * m + 2249 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3743.1, data_15_3743.2]

/-- Complete interval computation for depth 15, residue 3744. -/
theorem bounds_15_3744 : exactInterval 15 3744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3744 : oddCount 3744 15 = 4 ∧ acceleratedOrbit 15 3744 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3744) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3744.1, data_15_3744.2]

/-- Complete interval computation for depth 15, residue 3745. -/
theorem bounds_15_3745 : exactInterval 15 3745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3745 : oddCount 3745 15 = 8 ∧ acceleratedOrbit 15 3745 = 751 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3745) = 3 ^ 8 * m + 751 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3745.1, data_15_3745.2]

/-- Complete interval computation for depth 15, residue 3746. -/
theorem bounds_15_3746 : exactInterval 15 3746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3746 : oddCount 3746 15 = 7 ∧ acceleratedOrbit 15 3746 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3746) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3746.1, data_15_3746.2]

/-- Complete interval computation for depth 15, residue 3747. -/
theorem bounds_15_3747 : exactInterval 15 3747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3747 : oddCount 3747 15 = 7 ∧ acceleratedOrbit 15 3747 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3747) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3747.1, data_15_3747.2]

/-- Complete interval computation for depth 15, residue 3748. -/
theorem bounds_15_3748 : exactInterval 15 3748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3748 : oddCount 3748 15 = 10 ∧ acceleratedOrbit 15 3748 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3748) = 3 ^ 10 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3748.1, data_15_3748.2]

/-- Complete interval computation for depth 15, residue 3749. -/
theorem bounds_15_3749 : exactInterval 15 3749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3749 : oddCount 3749 15 = 10 ∧ acceleratedOrbit 15 3749 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3749) = 3 ^ 10 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3749.1, data_15_3749.2]

/-- Complete interval computation for depth 15, residue 3750. -/
theorem bounds_15_3750 : exactInterval 15 3750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3750 : oddCount 3750 15 = 10 ∧ acceleratedOrbit 15 3750 = 6767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3750) = 3 ^ 10 * m + 6767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3750.1, data_15_3750.2]

/-- Complete interval computation for depth 15, residue 3751. -/
theorem bounds_15_3751 : exactInterval 15 3751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3751 : oddCount 3751 15 = 10 ∧ acceleratedOrbit 15 3751 = 6763 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3751) = 3 ^ 10 * m + 6763 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3751.1, data_15_3751.2]

/-- Complete interval computation for depth 15, residue 3752. -/
theorem bounds_15_3752 : exactInterval 15 3752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3752 : oddCount 3752 15 = 4 ∧ acceleratedOrbit 15 3752 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3752) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3752.1, data_15_3752.2]

/-- Complete interval computation for depth 15, residue 3753. -/
theorem bounds_15_3753 : exactInterval 15 3753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3753 : oddCount 3753 15 = 10 ∧ acceleratedOrbit 15 3753 = 6766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3753) = 3 ^ 10 * m + 6766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3753.1, data_15_3753.2]

/-- Complete interval computation for depth 15, residue 3754. -/
theorem bounds_15_3754 : exactInterval 15 3754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3754 : oddCount 3754 15 = 4 ∧ acceleratedOrbit 15 3754 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3754) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3754.1, data_15_3754.2]

/-- Complete interval computation for depth 15, residue 3755. -/
theorem bounds_15_3755 : exactInterval 15 3755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3755 : oddCount 3755 15 = 9 ∧ acceleratedOrbit 15 3755 = 2258 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3755) = 3 ^ 9 * m + 2258 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3755.1, data_15_3755.2]

/-- Complete interval computation for depth 15, residue 3756. -/
theorem bounds_15_3756 : exactInterval 15 3756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3756 : oddCount 3756 15 = 8 ∧ acceleratedOrbit 15 3756 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3756) = 3 ^ 8 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3756.1, data_15_3756.2]

/-- Complete interval computation for depth 15, residue 3757. -/
theorem bounds_15_3757 : exactInterval 15 3757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3757 : oddCount 3757 15 = 8 ∧ acceleratedOrbit 15 3757 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3757) = 3 ^ 8 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3757.1, data_15_3757.2]

/-- Complete interval computation for depth 15, residue 3758. -/
theorem bounds_15_3758 : exactInterval 15 3758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3758 : oddCount 3758 15 = 8 ∧ acceleratedOrbit 15 3758 = 755 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3758) = 3 ^ 8 * m + 755 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3758.1, data_15_3758.2]

/-- Complete interval computation for depth 15, residue 3759. -/
theorem bounds_15_3759 : exactInterval 15 3759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3759 : oddCount 3759 15 = 7 ∧ acceleratedOrbit 15 3759 = 251 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3759) = 3 ^ 7 * m + 251 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3759.1, data_15_3759.2]

/-- Complete interval computation for depth 15, residue 3760. -/
theorem bounds_15_3760 : exactInterval 15 3760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3760 : oddCount 3760 15 = 7 ∧ acceleratedOrbit 15 3760 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3760) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3760.1, data_15_3760.2]

/-- Complete interval computation for depth 15, residue 3761. -/
theorem bounds_15_3761 : exactInterval 15 3761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3761 : oddCount 3761 15 = 5 ∧ acceleratedOrbit 15 3761 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3761) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3761.1, data_15_3761.2]

/-- Complete interval computation for depth 15, residue 3762. -/
theorem bounds_15_3762 : exactInterval 15 3762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3762 : oddCount 3762 15 = 5 ∧ acceleratedOrbit 15 3762 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3762) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3762.1, data_15_3762.2]

/-- Complete interval computation for depth 15, residue 3763. -/
theorem bounds_15_3763 : exactInterval 15 3763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3763 : oddCount 3763 15 = 5 ∧ acceleratedOrbit 15 3763 = 28 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3763) = 3 ^ 5 * m + 28 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3763.1, data_15_3763.2]

/-- Complete interval computation for depth 15, residue 3764. -/
theorem bounds_15_3764 : exactInterval 15 3764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3764 : oddCount 3764 15 = 7 ∧ acceleratedOrbit 15 3764 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3764) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3764.1, data_15_3764.2]

/-- Complete interval computation for depth 15, residue 3765. -/
theorem bounds_15_3765 : exactInterval 15 3765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3765 : oddCount 3765 15 = 7 ∧ acceleratedOrbit 15 3765 = 253 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3765) = 3 ^ 7 * m + 253 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3765.1, data_15_3765.2]

/-- Complete interval computation for depth 15, residue 3766. -/
theorem bounds_15_3766 : exactInterval 15 3766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3766 : oddCount 3766 15 = 10 ∧ acceleratedOrbit 15 3766 = 6794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3766) = 3 ^ 10 * m + 6794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3766.1, data_15_3766.2]

/-- Complete interval computation for depth 15, residue 3767. -/
theorem bounds_15_3767 : exactInterval 15 3767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3767 : oddCount 3767 15 = 10 ∧ acceleratedOrbit 15 3767 = 6794 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3767) = 3 ^ 10 * m + 6794 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3767.1, data_15_3767.2]

end Collatz.Research.PassageAtlas.Batch0115
