import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0206

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 6717. -/
theorem bounds_15_6717 : exactInterval 15 6717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6717 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6717) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6717 : oddCount 6717 15 = 9 ∧ acceleratedOrbit 15 6717 = 4040 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6717 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6717) = 3 ^ 9 * m + 4040 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6717.1, data_15_6717.2]

/-- Complete interval computation for depth 15, residue 6718. -/
theorem bounds_15_6718 : exactInterval 15 6718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6718 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6718) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6718 : oddCount 6718 15 = 7 ∧ acceleratedOrbit 15 6718 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6718 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6718) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6718.1, data_15_6718.2]

/-- Complete interval computation for depth 15, residue 6719. -/
theorem bounds_15_6719 : exactInterval 15 6719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6719) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6719 : oddCount 6719 15 = 7 ∧ acceleratedOrbit 15 6719 = 449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6719) = 3 ^ 7 * m + 449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6719.1, data_15_6719.2]

/-- Complete interval computation for depth 15, residue 6720. -/
theorem bounds_15_6720 : exactInterval 15 6720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6720 : oddCount 6720 15 = 6 ∧ acceleratedOrbit 15 6720 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6720) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6720.1, data_15_6720.2]

/-- Complete interval computation for depth 15, residue 6721. -/
theorem bounds_15_6721 : exactInterval 15 6721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6721 : oddCount 6721 15 = 5 ∧ acceleratedOrbit 15 6721 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6721) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6721.1, data_15_6721.2]

/-- Complete interval computation for depth 15, residue 6722. -/
theorem bounds_15_6722 : exactInterval 15 6722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6722 : oddCount 6722 15 = 5 ∧ acceleratedOrbit 15 6722 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6722) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6722.1, data_15_6722.2]

/-- Complete interval computation for depth 15, residue 6723. -/
theorem bounds_15_6723 : exactInterval 15 6723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6723 : oddCount 6723 15 = 5 ∧ acceleratedOrbit 15 6723 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6723) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6723.1, data_15_6723.2]

/-- Complete interval computation for depth 15, residue 6724. -/
theorem bounds_15_6724 : exactInterval 15 6724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6724 : oddCount 6724 15 = 5 ∧ acceleratedOrbit 15 6724 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6724) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6724.1, data_15_6724.2]

/-- Complete interval computation for depth 15, residue 6725. -/
theorem bounds_15_6725 : exactInterval 15 6725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6725 : oddCount 6725 15 = 5 ∧ acceleratedOrbit 15 6725 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6725) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6725.1, data_15_6725.2]

/-- Complete interval computation for depth 15, residue 6726. -/
theorem bounds_15_6726 : exactInterval 15 6726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6726 : oddCount 6726 15 = 5 ∧ acceleratedOrbit 15 6726 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6726) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6726.1, data_15_6726.2]

/-- Complete interval computation for depth 15, residue 6727. -/
theorem bounds_15_6727 : exactInterval 15 6727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6727) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6727 : oddCount 6727 15 = 9 ∧ acceleratedOrbit 15 6727 = 4043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6727) = 3 ^ 9 * m + 4043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6727.1, data_15_6727.2]

/-- Complete interval computation for depth 15, residue 6728. -/
theorem bounds_15_6728 : exactInterval 15 6728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6728 : oddCount 6728 15 = 5 ∧ acceleratedOrbit 15 6728 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6728) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6728.1, data_15_6728.2]

/-- Complete interval computation for depth 15, residue 6729. -/
theorem bounds_15_6729 : exactInterval 15 6729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6729 : oddCount 6729 15 = 8 ∧ acceleratedOrbit 15 6729 = 1349 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6729) = 3 ^ 8 * m + 1349 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6729.1, data_15_6729.2]

/-- Complete interval computation for depth 15, residue 6730. -/
theorem bounds_15_6730 : exactInterval 15 6730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6730 : oddCount 6730 15 = 5 ∧ acceleratedOrbit 15 6730 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6730) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6730.1, data_15_6730.2]

/-- Complete interval computation for depth 15, residue 6731. -/
theorem bounds_15_6731 : exactInterval 15 6731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6731 : oddCount 6731 15 = 5 ∧ acceleratedOrbit 15 6731 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6731) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6731.1, data_15_6731.2]

/-- Complete interval computation for depth 15, residue 6732. -/
theorem bounds_15_6732 : exactInterval 15 6732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6732 : oddCount 6732 15 = 5 ∧ acceleratedOrbit 15 6732 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6732) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6732.1, data_15_6732.2]

/-- Complete interval computation for depth 15, residue 6733. -/
theorem bounds_15_6733 : exactInterval 15 6733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6733 : oddCount 6733 15 = 5 ∧ acceleratedOrbit 15 6733 = 50 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6733) = 3 ^ 5 * m + 50 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6733.1, data_15_6733.2]

/-- Complete interval computation for depth 15, residue 6734. -/
theorem bounds_15_6734 : exactInterval 15 6734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6734 : oddCount 6734 15 = 9 ∧ acceleratedOrbit 15 6734 = 4049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6734) = 3 ^ 9 * m + 4049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6734.1, data_15_6734.2]

/-- Complete interval computation for depth 15, residue 6735. -/
theorem bounds_15_6735 : exactInterval 15 6735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6735 : oddCount 6735 15 = 9 ∧ acceleratedOrbit 15 6735 = 4049 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6735) = 3 ^ 9 * m + 4049 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6735.1, data_15_6735.2]

/-- Complete interval computation for depth 15, residue 6736. -/
theorem bounds_15_6736 : exactInterval 15 6736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6736 : oddCount 6736 15 = 6 ∧ acceleratedOrbit 15 6736 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6736) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6736.1, data_15_6736.2]

/-- Complete interval computation for depth 15, residue 6737. -/
theorem bounds_15_6737 : exactInterval 15 6737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6737 : oddCount 6737 15 = 11 ∧ acceleratedOrbit 15 6737 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6737) = 3 ^ 11 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6737.1, data_15_6737.2]

/-- Complete interval computation for depth 15, residue 6738. -/
theorem bounds_15_6738 : exactInterval 15 6738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6738 : oddCount 6738 15 = 11 ∧ acceleratedOrbit 15 6738 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6738) = 3 ^ 11 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6738.1, data_15_6738.2]

/-- Complete interval computation for depth 15, residue 6739. -/
theorem bounds_15_6739 : exactInterval 15 6739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6739 : oddCount 6739 15 = 11 ∧ acceleratedOrbit 15 6739 = 36449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6739) = 3 ^ 11 * m + 36449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6739.1, data_15_6739.2]

/-- Complete interval computation for depth 15, residue 6740. -/
theorem bounds_15_6740 : exactInterval 15 6740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6740 : oddCount 6740 15 = 6 ∧ acceleratedOrbit 15 6740 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6740) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6740.1, data_15_6740.2]

/-- Complete interval computation for depth 15, residue 6741. -/
theorem bounds_15_6741 : exactInterval 15 6741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6741 : oddCount 6741 15 = 6 ∧ acceleratedOrbit 15 6741 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6741) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6741.1, data_15_6741.2]

/-- Complete interval computation for depth 15, residue 6742. -/
theorem bounds_15_6742 : exactInterval 15 6742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6742 : oddCount 6742 15 = 8 ∧ acceleratedOrbit 15 6742 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6742) = 3 ^ 8 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6742.1, data_15_6742.2]

/-- Complete interval computation for depth 15, residue 6743. -/
theorem bounds_15_6743 : exactInterval 15 6743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6743 : oddCount 6743 15 = 8 ∧ acceleratedOrbit 15 6743 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6743) = 3 ^ 8 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6743.1, data_15_6743.2]

/-- Complete interval computation for depth 15, residue 6744. -/
theorem bounds_15_6744 : exactInterval 15 6744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6744 : oddCount 6744 15 = 6 ∧ acceleratedOrbit 15 6744 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6744) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6744.1, data_15_6744.2]

/-- Complete interval computation for depth 15, residue 6745. -/
theorem bounds_15_6745 : exactInterval 15 6745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6745 : oddCount 6745 15 = 8 ∧ acceleratedOrbit 15 6745 = 1352 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6745) = 3 ^ 8 * m + 1352 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6745.1, data_15_6745.2]

/-- Complete interval computation for depth 15, residue 6746. -/
theorem bounds_15_6746 : exactInterval 15 6746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6746 : oddCount 6746 15 = 6 ∧ acceleratedOrbit 15 6746 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6746) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6746.1, data_15_6746.2]

/-- Complete interval computation for depth 15, residue 6747. -/
theorem bounds_15_6747 : exactInterval 15 6747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6747 : oddCount 6747 15 = 9 ∧ acceleratedOrbit 15 6747 = 4054 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6747) = 3 ^ 9 * m + 4054 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6747.1, data_15_6747.2]

/-- Complete interval computation for depth 15, residue 6748. -/
theorem bounds_15_6748 : exactInterval 15 6748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6748 : oddCount 6748 15 = 6 ∧ acceleratedOrbit 15 6748 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6748) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6748.1, data_15_6748.2]

/-- Complete interval computation for depth 15, residue 6749. -/
theorem bounds_15_6749 : exactInterval 15 6749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_6749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 6749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_6749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_6749 : oddCount 6749 15 = 6 ∧ acceleratedOrbit 15 6749 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_6749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 6749) = 3 ^ 6 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_6749.1, data_15_6749.2]

end Collatz.Research.PassageAtlas.Batch0206
