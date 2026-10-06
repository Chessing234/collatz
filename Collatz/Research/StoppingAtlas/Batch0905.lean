import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0905

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 6717. -/
theorem bounds_13_6717 : exactInterval 13 6717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6717 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6717) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6717 : oddCount 6717 13 = 7 ∧ acceleratedOrbit 13 6717 = 1795 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6717 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6717) = 3 ^ 7 * m + 1795 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6717.1, data_13_6717.2]

/-- Complete interval computation for depth 13, residue 6718. -/
theorem bounds_13_6718 : exactInterval 13 6718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6718 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6718) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6718 : oddCount 6718 13 = 6 ∧ acceleratedOrbit 13 6718 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6718 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6718) = 3 ^ 6 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6718.1, data_13_6718.2]

/-- Complete interval computation for depth 13, residue 6719. -/
theorem bounds_13_6719 : exactInterval 13 6719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6719 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6719) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6719 : oddCount 6719 13 = 6 ∧ acceleratedOrbit 13 6719 = 598 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6719 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6719) = 3 ^ 6 * m + 598 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6719.1, data_13_6719.2]

/-- Complete interval computation for depth 13, residue 6720. -/
theorem bounds_13_6720 : exactInterval 13 6720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6720 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6720) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6720 : oddCount 6720 13 = 5 ∧ acceleratedOrbit 13 6720 = 202 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6720 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6720) = 3 ^ 5 * m + 202 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6720.1, data_13_6720.2]

/-- Complete interval computation for depth 13, residue 6721. -/
theorem bounds_13_6721 : exactInterval 13 6721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6721 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6721) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6721 : oddCount 6721 13 = 5 ∧ acceleratedOrbit 13 6721 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6721 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6721) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6721.1, data_13_6721.2]

/-- Complete interval computation for depth 13, residue 6722. -/
theorem bounds_13_6722 : exactInterval 13 6722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6722 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6722) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6722 : oddCount 6722 13 = 5 ∧ acceleratedOrbit 13 6722 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6722 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6722) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6722.1, data_13_6722.2]

/-- Complete interval computation for depth 13, residue 6723. -/
theorem bounds_13_6723 : exactInterval 13 6723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6723 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6723) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6723 : oddCount 6723 13 = 5 ∧ acceleratedOrbit 13 6723 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6723 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6723) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6723.1, data_13_6723.2]

/-- Complete interval computation for depth 13, residue 6724. -/
theorem bounds_13_6724 : exactInterval 13 6724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6724 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6724) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6724 : oddCount 6724 13 = 5 ∧ acceleratedOrbit 13 6724 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6724 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6724) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6724.1, data_13_6724.2]

/-- Complete interval computation for depth 13, residue 6725. -/
theorem bounds_13_6725 : exactInterval 13 6725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6725 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6725) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6725 : oddCount 6725 13 = 5 ∧ acceleratedOrbit 13 6725 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6725 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6725) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6725.1, data_13_6725.2]

/-- Complete interval computation for depth 13, residue 6726. -/
theorem bounds_13_6726 : exactInterval 13 6726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6726 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6726) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6726 : oddCount 6726 13 = 5 ∧ acceleratedOrbit 13 6726 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6726 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6726) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6726.1, data_13_6726.2]

/-- Complete interval computation for depth 13, residue 6727. -/
theorem bounds_13_6727 : exactInterval 13 6727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6727 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6727) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6727 : oddCount 6727 13 = 8 ∧ acceleratedOrbit 13 6727 = 5390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6727 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6727) = 3 ^ 8 * m + 5390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6727.1, data_13_6727.2]

/-- Complete interval computation for depth 13, residue 6728. -/
theorem bounds_13_6728 : exactInterval 13 6728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6728 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6728) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6728 : oddCount 6728 13 = 5 ∧ acceleratedOrbit 13 6728 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6728 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6728) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6728.1, data_13_6728.2]

/-- Complete interval computation for depth 13, residue 6729. -/
theorem bounds_13_6729 : exactInterval 13 6729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6729 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6729) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6729 : oddCount 6729 13 = 6 ∧ acceleratedOrbit 13 6729 = 599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6729 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6729) = 3 ^ 6 * m + 599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6729.1, data_13_6729.2]

/-- Complete interval computation for depth 13, residue 6730. -/
theorem bounds_13_6730 : exactInterval 13 6730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6730 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6730) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6730 : oddCount 6730 13 = 5 ∧ acceleratedOrbit 13 6730 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6730 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6730) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6730.1, data_13_6730.2]

/-- Complete interval computation for depth 13, residue 6731. -/
theorem bounds_13_6731 : exactInterval 13 6731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_6731 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 6731) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_6731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_6731 : oddCount 6731 13 = 5 ∧ acceleratedOrbit 13 6731 = 200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_6731 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 6731) = 3 ^ 5 * m + 200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_6731.1, data_13_6731.2]

end Collatz.Research.StoppingAtlas.Batch0905
