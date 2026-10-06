import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0378

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2718. -/
theorem bounds_12_2718 : exactInterval 12 2718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2718 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2718) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2718 : oddCount 2718 12 = 7 ∧ acceleratedOrbit 12 2718 = 1453 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2718 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2718) = 3 ^ 7 * m + 1453 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2718.1, data_12_2718.2]

/-- Complete interval computation for depth 12, residue 2719. -/
theorem bounds_12_2719 : exactInterval 12 2719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2719 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2719) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2719 : oddCount 2719 12 = 8 ∧ acceleratedOrbit 12 2719 = 4357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2719 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2719) = 3 ^ 8 * m + 4357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2719.1, data_12_2719.2]

/-- Complete interval computation for depth 12, residue 2720. -/
theorem bounds_12_2720 : exactInterval 12 2720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2720 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2720) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2720 : oddCount 2720 12 = 1 ∧ acceleratedOrbit 12 2720 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2720 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2720) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2720.1, data_12_2720.2]

/-- Complete interval computation for depth 12, residue 2721. -/
theorem bounds_12_2721 : exactInterval 12 2721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2721 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2721) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2721 : oddCount 2721 12 = 8 ∧ acceleratedOrbit 12 2721 = 4364 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2721 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2721) = 3 ^ 8 * m + 4364 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2721.1, data_12_2721.2]

/-- Complete interval computation for depth 12, residue 2722. -/
theorem bounds_12_2722 : exactInterval 12 2722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2722 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2722) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2722 : oddCount 2722 12 = 8 ∧ acceleratedOrbit 12 2722 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2722 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2722) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2722.1, data_12_2722.2]

/-- Complete interval computation for depth 12, residue 2723. -/
theorem bounds_12_2723 : exactInterval 12 2723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2723 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2723) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2723 : oddCount 2723 12 = 8 ∧ acceleratedOrbit 12 2723 = 4373 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2723 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2723) = 3 ^ 8 * m + 4373 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2723.1, data_12_2723.2]

/-- Complete interval computation for depth 12, residue 2724. -/
theorem bounds_12_2724 : exactInterval 12 2724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2724 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2724) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2724 : oddCount 2724 12 = 9 ∧ acceleratedOrbit 12 2724 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2724 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2724) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2724.1, data_12_2724.2]

/-- Complete interval computation for depth 12, residue 2725. -/
theorem bounds_12_2725 : exactInterval 12 2725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2725 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2725) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2725 : oddCount 2725 12 = 9 ∧ acceleratedOrbit 12 2725 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2725 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2725) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2725.1, data_12_2725.2]

/-- Complete interval computation for depth 12, residue 2726. -/
theorem bounds_12_2726 : exactInterval 12 2726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2726 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2726) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2726 : oddCount 2726 12 = 9 ∧ acceleratedOrbit 12 2726 = 13121 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2726 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2726) = 3 ^ 9 * m + 13121 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2726.1, data_12_2726.2]

/-- Complete interval computation for depth 12, residue 2727. -/
theorem bounds_12_2727 : exactInterval 12 2727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2727 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2727) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2727 : oddCount 2727 12 = 9 ∧ acceleratedOrbit 12 2727 = 13112 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2727 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2727) = 3 ^ 9 * m + 13112 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2727.1, data_12_2727.2]

/-- Complete interval computation for depth 12, residue 2728. -/
theorem bounds_12_2728 : exactInterval 12 2728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2728 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2728) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2728 : oddCount 2728 12 = 1 ∧ acceleratedOrbit 12 2728 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2728 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2728) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2728.1, data_12_2728.2]

/-- Complete interval computation for depth 12, residue 2729. -/
theorem bounds_12_2729 : exactInterval 12 2729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2729 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2729) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2729 : oddCount 2729 12 = 11 ∧ acceleratedOrbit 12 2729 = 118097 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2729 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2729) = 3 ^ 11 * m + 118097 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2729.1, data_12_2729.2]

/-- Complete interval computation for depth 12, residue 2730. -/
theorem bounds_12_2730 : exactInterval 12 2730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2730 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2730) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2730 : oddCount 2730 12 = 1 ∧ acceleratedOrbit 12 2730 = 2 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2730 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2730) = 3 ^ 1 * m + 2 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2730.1, data_12_2730.2]

/-- Complete interval computation for depth 12, residue 2731. -/
theorem bounds_12_2731 : exactInterval 12 2731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2731 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2731) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2731 : oddCount 2731 12 = 7 ∧ acceleratedOrbit 12 2731 = 1460 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2731 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2731) = 3 ^ 7 * m + 1460 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2731.1, data_12_2731.2]

/-- Complete interval computation for depth 12, residue 2732. -/
theorem bounds_12_2732 : exactInterval 12 2732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2732 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2732) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2732 : oddCount 2732 12 = 6 ∧ acceleratedOrbit 12 2732 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2732 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2732) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2732.1, data_12_2732.2]

/-- Complete interval computation for depth 12, residue 2733. -/
theorem bounds_12_2733 : exactInterval 12 2733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2733 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2733) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2733 : oddCount 2733 12 = 6 ∧ acceleratedOrbit 12 2733 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2733 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2733) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2733.1, data_12_2733.2]

end Collatz.Research.StoppingAtlas.Batch0378
