import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0207

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6750. -/
theorem bounds_15_6750 : exactInterval 15 6750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6750 : oddCount 6750 15 = 10 ∧ acceleratedOrbit 15 6750 = 12170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6750) = 3 ^ 10 * m + 12170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6750.1, data_15_6750.2]

/-- Complete interval computation for depth 15, residue 6751. -/
theorem bounds_15_6751 : exactInterval 15 6751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6751 : oddCount 6751 15 = 10 ∧ acceleratedOrbit 15 6751 = 12170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6751) = 3 ^ 10 * m + 12170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6751.1, data_15_6751.2]

/-- Complete interval computation for depth 15, residue 6752. -/
theorem bounds_15_6752 : exactInterval 15 6752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6752 : oddCount 6752 15 = 6 ∧ acceleratedOrbit 15 6752 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6752) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6752.1, data_15_6752.2]

/-- Complete interval computation for depth 15, residue 6753. -/
theorem bounds_15_6753 : exactInterval 15 6753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6753 : oddCount 6753 15 = 7 ∧ acceleratedOrbit 15 6753 = 451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6753) = 3 ^ 7 * m + 451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6753.1, data_15_6753.2]

/-- Complete interval computation for depth 15, residue 6754. -/
theorem bounds_15_6754 : exactInterval 15 6754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6754 : oddCount 6754 15 = 7 ∧ acceleratedOrbit 15 6754 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6754) = 3 ^ 7 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6754.1, data_15_6754.2]

/-- Complete interval computation for depth 15, residue 6755. -/
theorem bounds_15_6755 : exactInterval 15 6755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6755 : oddCount 6755 15 = 7 ∧ acceleratedOrbit 15 6755 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6755) = 3 ^ 7 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6755.1, data_15_6755.2]

/-- Complete interval computation for depth 15, residue 6756. -/
theorem bounds_15_6756 : exactInterval 15 6756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6756 : oddCount 6756 15 = 7 ∧ acceleratedOrbit 15 6756 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6756) = 3 ^ 7 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6756.1, data_15_6756.2]

/-- Complete interval computation for depth 15, residue 6757. -/
theorem bounds_15_6757 : exactInterval 15 6757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6757 : oddCount 6757 15 = 7 ∧ acceleratedOrbit 15 6757 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6757) = 3 ^ 7 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6757.1, data_15_6757.2]

/-- Complete interval computation for depth 15, residue 6758. -/
theorem bounds_15_6758 : exactInterval 15 6758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6758 : oddCount 6758 15 = 7 ∧ acceleratedOrbit 15 6758 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6758) = 3 ^ 7 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6758.1, data_15_6758.2]

/-- Complete interval computation for depth 15, residue 6759. -/
theorem bounds_15_6759 : exactInterval 15 6759 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6759) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6759 : oddCount 6759 15 = 9 ∧ acceleratedOrbit 15 6759 = 4061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6759) = 3 ^ 9 * m + 4061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6759.1, data_15_6759.2]

/-- Complete interval computation for depth 15, residue 6760. -/
theorem bounds_15_6760 : exactInterval 15 6760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6760 : oddCount 6760 15 = 6 ∧ acceleratedOrbit 15 6760 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6760) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6760.1, data_15_6760.2]

/-- Complete interval computation for depth 15, residue 6761. -/
theorem bounds_15_6761 : exactInterval 15 6761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6761 : oddCount 6761 15 = 9 ∧ acceleratedOrbit 15 6761 = 4063 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6761) = 3 ^ 9 * m + 4063 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6761.1, data_15_6761.2]

/-- Complete interval computation for depth 15, residue 6762. -/
theorem bounds_15_6762 : exactInterval 15 6762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6762 : oddCount 6762 15 = 6 ∧ acceleratedOrbit 15 6762 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6762) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6762.1, data_15_6762.2]

/-- Complete interval computation for depth 15, residue 6763. -/
theorem bounds_15_6763 : exactInterval 15 6763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6763 : oddCount 6763 15 = 7 ∧ acceleratedOrbit 15 6763 = 452 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6763) = 3 ^ 7 * m + 452 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6763.1, data_15_6763.2]

/-- Complete interval computation for depth 15, residue 6764. -/
theorem bounds_15_6764 : exactInterval 15 6764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6764 : oddCount 6764 15 = 9 ∧ acceleratedOrbit 15 6764 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6764) = 3 ^ 9 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6764.1, data_15_6764.2]

/-- Complete interval computation for depth 15, residue 6765. -/
theorem bounds_15_6765 : exactInterval 15 6765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6765 : oddCount 6765 15 = 9 ∧ acceleratedOrbit 15 6765 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6765) = 3 ^ 9 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6765.1, data_15_6765.2]

/-- Complete interval computation for depth 15, residue 6766. -/
theorem bounds_15_6766 : exactInterval 15 6766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6766 : oddCount 6766 15 = 9 ∧ acceleratedOrbit 15 6766 = 4067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6766) = 3 ^ 9 * m + 4067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6766.1, data_15_6766.2]

/-- Complete interval computation for depth 15, residue 6767. -/
theorem bounds_15_6767 : exactInterval 15 6767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6767 : oddCount 6767 15 = 10 ∧ acceleratedOrbit 15 6767 = 12197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6767) = 3 ^ 10 * m + 12197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6767.1, data_15_6767.2]

/-- Complete interval computation for depth 15, residue 6768. -/
theorem bounds_15_6768 : exactInterval 15 6768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6768 : oddCount 6768 15 = 6 ∧ acceleratedOrbit 15 6768 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6768) = 3 ^ 6 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6768.1, data_15_6768.2]

/-- Complete interval computation for depth 15, residue 6769. -/
theorem bounds_15_6769 : exactInterval 15 6769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6769 : oddCount 6769 15 = 6 ∧ acceleratedOrbit 15 6769 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6769) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6769.1, data_15_6769.2]

/-- Complete interval computation for depth 15, residue 6770. -/
theorem bounds_15_6770 : exactInterval 15 6770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6770 : oddCount 6770 15 = 9 ∧ acceleratedOrbit 15 6770 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6770) = 3 ^ 9 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6770.1, data_15_6770.2]

/-- Complete interval computation for depth 15, residue 6771. -/
theorem bounds_15_6771 : exactInterval 15 6771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6771 : oddCount 6771 15 = 9 ∧ acceleratedOrbit 15 6771 = 4070 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6771) = 3 ^ 9 * m + 4070 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6771.1, data_15_6771.2]

/-- Complete interval computation for depth 15, residue 6772. -/
theorem bounds_15_6772 : exactInterval 15 6772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6772 : oddCount 6772 15 = 6 ∧ acceleratedOrbit 15 6772 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6772) = 3 ^ 6 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6772.1, data_15_6772.2]

/-- Complete interval computation for depth 15, residue 6773. -/
theorem bounds_15_6773 : exactInterval 15 6773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6773 : oddCount 6773 15 = 6 ∧ acceleratedOrbit 15 6773 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6773) = 3 ^ 6 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6773.1, data_15_6773.2]

/-- Complete interval computation for depth 15, residue 6774. -/
theorem bounds_15_6774 : exactInterval 15 6774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6774 : oddCount 6774 15 = 6 ∧ acceleratedOrbit 15 6774 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6774) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6774.1, data_15_6774.2]

/-- Complete interval computation for depth 15, residue 6775. -/
theorem bounds_15_6775 : exactInterval 15 6775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6775 : oddCount 6775 15 = 6 ∧ acceleratedOrbit 15 6775 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6775) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6775.1, data_15_6775.2]

/-- Complete interval computation for depth 15, residue 6776. -/
theorem bounds_15_6776 : exactInterval 15 6776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6776 : oddCount 6776 15 = 6 ∧ acceleratedOrbit 15 6776 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6776) = 3 ^ 6 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6776.1, data_15_6776.2]

/-- Complete interval computation for depth 15, residue 6777. -/
theorem bounds_15_6777 : exactInterval 15 6777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6777 : oddCount 6777 15 = 8 ∧ acceleratedOrbit 15 6777 = 1358 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6777) = 3 ^ 8 * m + 1358 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6777.1, data_15_6777.2]

/-- Complete interval computation for depth 15, residue 6778. -/
theorem bounds_15_6778 : exactInterval 15 6778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6778 : oddCount 6778 15 = 6 ∧ acceleratedOrbit 15 6778 = 151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6778) = 3 ^ 6 * m + 151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6778.1, data_15_6778.2]

/-- Complete interval computation for depth 15, residue 6779. -/
theorem bounds_15_6779 : exactInterval 15 6779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6779 : oddCount 6779 15 = 9 ∧ acceleratedOrbit 15 6779 = 4076 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6779) = 3 ^ 9 * m + 4076 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6779.1, data_15_6779.2]

/-- Complete interval computation for depth 15, residue 6780. -/
theorem bounds_15_6780 : exactInterval 15 6780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6780 : oddCount 6780 15 = 10 ∧ acceleratedOrbit 15 6780 = 12226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6780) = 3 ^ 10 * m + 12226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6780.1, data_15_6780.2]

/-- Complete interval computation for depth 15, residue 6781. -/
theorem bounds_15_6781 : exactInterval 15 6781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6781 : oddCount 6781 15 = 10 ∧ acceleratedOrbit 15 6781 = 12226 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6781) = 3 ^ 10 * m + 12226 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6781.1, data_15_6781.2]

end Collatz.Research.PassageAtlas.Batch0207
