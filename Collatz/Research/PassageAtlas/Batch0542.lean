import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0542

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 17727. -/
theorem bounds_15_17727 : exactInterval 15 17727 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17727) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17727 : oddCount 17727 15 = 9 ∧ acceleratedOrbit 15 17727 = 10649 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17727) = 3 ^ 9 * m + 10649 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17727.1, data_15_17727.2]

/-- Complete interval computation for depth 15, residue 17728. -/
theorem bounds_15_17728 : exactInterval 15 17728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17728 : oddCount 17728 15 = 2 ∧ acceleratedOrbit 15 17728 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17728) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17728.1, data_15_17728.2]

/-- Complete interval computation for depth 15, residue 17729. -/
theorem bounds_15_17729 : exactInterval 15 17729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17729 : oddCount 17729 15 = 8 ∧ acceleratedOrbit 15 17729 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17729) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17729.1, data_15_17729.2]

/-- Complete interval computation for depth 15, residue 17730. -/
theorem bounds_15_17730 : exactInterval 15 17730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17730 : oddCount 17730 15 = 9 ∧ acceleratedOrbit 15 17730 = 10655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17730) = 3 ^ 9 * m + 10655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17730.1, data_15_17730.2]

/-- Complete interval computation for depth 15, residue 17731. -/
theorem bounds_15_17731 : exactInterval 15 17731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17731 : oddCount 17731 15 = 9 ∧ acceleratedOrbit 15 17731 = 10655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17731) = 3 ^ 9 * m + 10655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17731.1, data_15_17731.2]

/-- Complete interval computation for depth 15, residue 17732. -/
theorem bounds_15_17732 : exactInterval 15 17732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17732 : oddCount 17732 15 = 8 ∧ acceleratedOrbit 15 17732 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17732) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17732.1, data_15_17732.2]

/-- Complete interval computation for depth 15, residue 17733. -/
theorem bounds_15_17733 : exactInterval 15 17733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17733 : oddCount 17733 15 = 8 ∧ acceleratedOrbit 15 17733 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17733) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17733.1, data_15_17733.2]

/-- Complete interval computation for depth 15, residue 17734. -/
theorem bounds_15_17734 : exactInterval 15 17734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17734 : oddCount 17734 15 = 8 ∧ acceleratedOrbit 15 17734 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17734) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17734.1, data_15_17734.2]

/-- Complete interval computation for depth 15, residue 17735. -/
theorem bounds_15_17735 : exactInterval 15 17735 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17735) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17735 : oddCount 17735 15 = 9 ∧ acceleratedOrbit 15 17735 = 10654 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17735) = 3 ^ 9 * m + 10654 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17735.1, data_15_17735.2]

/-- Complete interval computation for depth 15, residue 17736. -/
theorem bounds_15_17736 : exactInterval 15 17736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17736 : oddCount 17736 15 = 10 ∧ acceleratedOrbit 15 17736 = 31985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17736) = 3 ^ 10 * m + 31985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17736.1, data_15_17736.2]

/-- Complete interval computation for depth 15, residue 17737. -/
theorem bounds_15_17737 : exactInterval 15 17737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17737 : oddCount 17737 15 = 7 ∧ acceleratedOrbit 15 17737 = 1184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17737) = 3 ^ 7 * m + 1184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17737.1, data_15_17737.2]

/-- Complete interval computation for depth 15, residue 17738. -/
theorem bounds_15_17738 : exactInterval 15 17738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17738 : oddCount 17738 15 = 10 ∧ acceleratedOrbit 15 17738 = 31985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17738) = 3 ^ 10 * m + 31985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17738.1, data_15_17738.2]

/-- Complete interval computation for depth 15, residue 17739. -/
theorem bounds_15_17739 : exactInterval 15 17739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17739 : oddCount 17739 15 = 8 ∧ acceleratedOrbit 15 17739 = 3554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17739) = 3 ^ 8 * m + 3554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17739.1, data_15_17739.2]

/-- Complete interval computation for depth 15, residue 17740. -/
theorem bounds_15_17740 : exactInterval 15 17740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17740 : oddCount 17740 15 = 10 ∧ acceleratedOrbit 15 17740 = 31985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17740) = 3 ^ 10 * m + 31985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17740.1, data_15_17740.2]

/-- Complete interval computation for depth 15, residue 17741. -/
theorem bounds_15_17741 : exactInterval 15 17741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17741 : oddCount 17741 15 = 10 ∧ acceleratedOrbit 15 17741 = 31985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17741) = 3 ^ 10 * m + 31985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17741.1, data_15_17741.2]

/-- Complete interval computation for depth 15, residue 17742. -/
theorem bounds_15_17742 : exactInterval 15 17742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17742 : oddCount 17742 15 = 8 ∧ acceleratedOrbit 15 17742 = 3553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17742) = 3 ^ 8 * m + 3553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17742.1, data_15_17742.2]

/-- Complete interval computation for depth 15, residue 17743. -/
theorem bounds_15_17743 : exactInterval 15 17743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17743 : oddCount 17743 15 = 8 ∧ acceleratedOrbit 15 17743 = 3553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17743) = 3 ^ 8 * m + 3553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17743.1, data_15_17743.2]

/-- Complete interval computation for depth 15, residue 17744. -/
theorem bounds_15_17744 : exactInterval 15 17744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17744 : oddCount 17744 15 = 2 ∧ acceleratedOrbit 15 17744 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17744) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17744.1, data_15_17744.2]

/-- Complete interval computation for depth 15, residue 17745. -/
theorem bounds_15_17745 : exactInterval 15 17745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17745 : oddCount 17745 15 = 10 ∧ acceleratedOrbit 15 17745 = 31985 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17745) = 3 ^ 10 * m + 31985 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17745.1, data_15_17745.2]

/-- Complete interval computation for depth 15, residue 17746. -/
theorem bounds_15_17746 : exactInterval 15 17746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17746 : oddCount 17746 15 = 12 ∧ acceleratedOrbit 15 17746 = 287864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17746) = 3 ^ 12 * m + 287864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17746.1, data_15_17746.2]

/-- Complete interval computation for depth 15, residue 17747. -/
theorem bounds_15_17747 : exactInterval 15 17747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17747 : oddCount 17747 15 = 12 ∧ acceleratedOrbit 15 17747 = 287864 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17747) = 3 ^ 12 * m + 287864 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17747.1, data_15_17747.2]

/-- Complete interval computation for depth 15, residue 17748. -/
theorem bounds_15_17748 : exactInterval 15 17748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17748 : oddCount 17748 15 = 2 ∧ acceleratedOrbit 15 17748 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17748) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17748.1, data_15_17748.2]

/-- Complete interval computation for depth 15, residue 17749. -/
theorem bounds_15_17749 : exactInterval 15 17749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17749 : oddCount 17749 15 = 2 ∧ acceleratedOrbit 15 17749 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17749) = 3 ^ 2 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17749.1, data_15_17749.2]

/-- Complete interval computation for depth 15, residue 17750. -/
theorem bounds_15_17750 : exactInterval 15 17750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17750 : oddCount 17750 15 = 6 ∧ acceleratedOrbit 15 17750 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17750) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17750.1, data_15_17750.2]

/-- Complete interval computation for depth 15, residue 17751. -/
theorem bounds_15_17751 : exactInterval 15 17751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17751 : oddCount 17751 15 = 6 ∧ acceleratedOrbit 15 17751 = 395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17751) = 3 ^ 6 * m + 395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17751.1, data_15_17751.2]

/-- Complete interval computation for depth 15, residue 17752. -/
theorem bounds_15_17752 : exactInterval 15 17752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17752 : oddCount 17752 15 = 7 ∧ acceleratedOrbit 15 17752 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17752) = 3 ^ 7 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17752.1, data_15_17752.2]

/-- Complete interval computation for depth 15, residue 17753. -/
theorem bounds_15_17753 : exactInterval 15 17753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17753 : oddCount 17753 15 = 8 ∧ acceleratedOrbit 15 17753 = 3557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17753) = 3 ^ 8 * m + 3557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17753.1, data_15_17753.2]

/-- Complete interval computation for depth 15, residue 17754. -/
theorem bounds_15_17754 : exactInterval 15 17754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17754 : oddCount 17754 15 = 7 ∧ acceleratedOrbit 15 17754 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17754) = 3 ^ 7 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17754.1, data_15_17754.2]

/-- Complete interval computation for depth 15, residue 17755. -/
theorem bounds_15_17755 : exactInterval 15 17755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17755 : oddCount 17755 15 = 9 ∧ acceleratedOrbit 15 17755 = 10667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17755) = 3 ^ 9 * m + 10667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17755.1, data_15_17755.2]

/-- Complete interval computation for depth 15, residue 17756. -/
theorem bounds_15_17756 : exactInterval 15 17756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17756 : oddCount 17756 15 = 7 ∧ acceleratedOrbit 15 17756 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17756) = 3 ^ 7 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17756.1, data_15_17756.2]

/-- Complete interval computation for depth 15, residue 17757. -/
theorem bounds_15_17757 : exactInterval 15 17757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17757 : oddCount 17757 15 = 7 ∧ acceleratedOrbit 15 17757 = 1187 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17757) = 3 ^ 7 * m + 1187 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17757.1, data_15_17757.2]

/-- Complete interval computation for depth 15, residue 17758. -/
theorem bounds_15_17758 : exactInterval 15 17758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17758 : oddCount 17758 15 = 8 ∧ acceleratedOrbit 15 17758 = 3557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17758) = 3 ^ 8 * m + 3557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17758.1, data_15_17758.2]

/-- Complete interval computation for depth 15, residue 17759. -/
theorem bounds_15_17759 : exactInterval 15 17759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_17759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 17759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_17759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_17759 : oddCount 17759 15 = 8 ∧ acceleratedOrbit 15 17759 = 3557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_17759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 17759) = 3 ^ 8 * m + 3557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_17759.1, data_15_17759.2]

end Collatz.Research.PassageAtlas.Batch0542
