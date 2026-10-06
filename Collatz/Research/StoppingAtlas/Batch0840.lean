import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0840

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5719. -/
theorem bounds_13_5719 : exactInterval 13 5719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5719 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5719) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5719 : oddCount 5719 13 = 7 ∧ acceleratedOrbit 13 5719 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5719 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5719) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5719.1, data_13_5719.2]

/-- Complete interval computation for depth 13, residue 5720. -/
theorem bounds_13_5720 : exactInterval 13 5720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5720 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5720) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5720 : oddCount 5720 13 = 6 ∧ acceleratedOrbit 13 5720 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5720 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5720) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5720.1, data_13_5720.2]

/-- Complete interval computation for depth 13, residue 5721. -/
theorem bounds_13_5721 : exactInterval 13 5721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5721 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5721) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5721 : oddCount 5721 13 = 7 ∧ acceleratedOrbit 13 5721 = 1529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5721 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5721) = 3 ^ 7 * m + 1529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5721.1, data_13_5721.2]

/-- Complete interval computation for depth 13, residue 5722. -/
theorem bounds_13_5722 : exactInterval 13 5722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5722 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5722) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5722 : oddCount 5722 13 = 6 ∧ acceleratedOrbit 13 5722 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5722 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5722) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5722.1, data_13_5722.2]

/-- Complete interval computation for depth 13, residue 5723. -/
theorem bounds_13_5723 : exactInterval 13 5723 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5723 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5723) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5723 : oddCount 5723 13 = 8 ∧ acceleratedOrbit 13 5723 = 4585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5723 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5723) = 3 ^ 8 * m + 4585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5723.1, data_13_5723.2]

/-- Complete interval computation for depth 13, residue 5724. -/
theorem bounds_13_5724 : exactInterval 13 5724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5724 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5724) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5724 : oddCount 5724 13 = 6 ∧ acceleratedOrbit 13 5724 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5724 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5724) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5724.1, data_13_5724.2]

/-- Complete interval computation for depth 13, residue 5725. -/
theorem bounds_13_5725 : exactInterval 13 5725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5725 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5725) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5725 : oddCount 5725 13 = 6 ∧ acceleratedOrbit 13 5725 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5725 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5725) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5725.1, data_13_5725.2]

/-- Complete interval computation for depth 13, residue 5726. -/
theorem bounds_13_5726 : exactInterval 13 5726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5726 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5726) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5726 : oddCount 5726 13 = 8 ∧ acceleratedOrbit 13 5726 = 4589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5726 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5726) = 3 ^ 8 * m + 4589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5726.1, data_13_5726.2]

/-- Complete interval computation for depth 13, residue 5727. -/
theorem bounds_13_5727 : exactInterval 13 5727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5727 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5727) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5727 : oddCount 5727 13 = 8 ∧ acceleratedOrbit 13 5727 = 4589 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5727 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5727) = 3 ^ 8 * m + 4589 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5727.1, data_13_5727.2]

/-- Complete interval computation for depth 13, residue 5728. -/
theorem bounds_13_5728 : exactInterval 13 5728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5728 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5728) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5728 : oddCount 5728 13 = 3 ∧ acceleratedOrbit 13 5728 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5728 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5728) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5728.1, data_13_5728.2]

/-- Complete interval computation for depth 13, residue 5729. -/
theorem bounds_13_5729 : exactInterval 13 5729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5729 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5729) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5729 : oddCount 5729 13 = 5 ∧ acceleratedOrbit 13 5729 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5729 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5729) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5729.1, data_13_5729.2]

/-- Complete interval computation for depth 13, residue 5730. -/
theorem bounds_13_5730 : exactInterval 13 5730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5730 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5730) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5730 : oddCount 5730 13 = 6 ∧ acceleratedOrbit 13 5730 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5730 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5730) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5730.1, data_13_5730.2]

/-- Complete interval computation for depth 13, residue 5731. -/
theorem bounds_13_5731 : exactInterval 13 5731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5731 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5731) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5731 : oddCount 5731 13 = 6 ∧ acceleratedOrbit 13 5731 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5731 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5731) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5731.1, data_13_5731.2]

/-- Complete interval computation for depth 13, residue 5732. -/
theorem bounds_13_5732 : exactInterval 13 5732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5732 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5732) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5732 : oddCount 5732 13 = 6 ∧ acceleratedOrbit 13 5732 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5732 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5732) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5732.1, data_13_5732.2]

/-- Complete interval computation for depth 13, residue 5733. -/
theorem bounds_13_5733 : exactInterval 13 5733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5733 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5733) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5733 : oddCount 5733 13 = 6 ∧ acceleratedOrbit 13 5733 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5733 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5733) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5733.1, data_13_5733.2]

end Collatz.Research.StoppingAtlas.Batch0840
