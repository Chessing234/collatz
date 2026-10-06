import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0645

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 2723. -/
theorem bounds_13_2723 : exactInterval 13 2723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2723 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2723) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2723 : oddCount 2723 13 = 9 ∧ acceleratedOrbit 13 2723 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2723 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2723) = 3 ^ 9 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2723.1, data_13_2723.2]

/-- Complete interval computation for depth 13, residue 2724. -/
theorem bounds_13_2724 : exactInterval 13 2724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2724 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2724) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2724 : oddCount 2724 13 = 10 ∧ acceleratedOrbit 13 2724 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2724 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2724) = 3 ^ 10 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2724.1, data_13_2724.2]

/-- Complete interval computation for depth 13, residue 2725. -/
theorem bounds_13_2725 : exactInterval 13 2725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2725 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2725) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2725 : oddCount 2725 13 = 10 ∧ acceleratedOrbit 13 2725 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2725 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2725) = 3 ^ 10 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2725.1, data_13_2725.2]

/-- Complete interval computation for depth 13, residue 2726. -/
theorem bounds_13_2726 : exactInterval 13 2726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2726 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2726) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2726 : oddCount 2726 13 = 10 ∧ acceleratedOrbit 13 2726 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2726 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2726) = 3 ^ 10 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2726.1, data_13_2726.2]

/-- Complete interval computation for depth 13, residue 2727. -/
theorem bounds_13_2727 : exactInterval 13 2727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2727 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2727) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2727 : oddCount 2727 13 = 9 ∧ acceleratedOrbit 13 2727 = 6556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2727 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2727) = 3 ^ 9 * m + 6556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2727.1, data_13_2727.2]

/-- Complete interval computation for depth 13, residue 2728. -/
theorem bounds_13_2728 : exactInterval 13 2728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2728 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2728) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2728 : oddCount 2728 13 = 1 ∧ acceleratedOrbit 13 2728 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2728 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2728) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2728.1, data_13_2728.2]

/-- Complete interval computation for depth 13, residue 2729. -/
theorem bounds_13_2729 : exactInterval 13 2729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2729 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2729) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2729 : oddCount 2729 13 = 12 ∧ acceleratedOrbit 13 2729 = 177146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2729 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2729) = 3 ^ 12 * m + 177146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2729.1, data_13_2729.2]

/-- Complete interval computation for depth 13, residue 2730. -/
theorem bounds_13_2730 : exactInterval 13 2730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2730 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2730) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2730 : oddCount 2730 13 = 1 ∧ acceleratedOrbit 13 2730 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2730 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2730) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2730.1, data_13_2730.2]

/-- Complete interval computation for depth 13, residue 2731. -/
theorem bounds_13_2731 : exactInterval 13 2731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2731 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2731) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2731 : oddCount 2731 13 = 7 ∧ acceleratedOrbit 13 2731 = 730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2731 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2731) = 3 ^ 7 * m + 730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2731.1, data_13_2731.2]

/-- Complete interval computation for depth 13, residue 2732. -/
theorem bounds_13_2732 : exactInterval 13 2732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2732 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2732) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2732 : oddCount 2732 13 = 6 ∧ acceleratedOrbit 13 2732 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2732 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2732) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2732.1, data_13_2732.2]

/-- Complete interval computation for depth 13, residue 2733. -/
theorem bounds_13_2733 : exactInterval 13 2733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2733 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2733) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2733 : oddCount 2733 13 = 6 ∧ acceleratedOrbit 13 2733 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2733 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2733) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2733.1, data_13_2733.2]

/-- Complete interval computation for depth 13, residue 2734. -/
theorem bounds_13_2734 : exactInterval 13 2734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2734 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2734) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2734 : oddCount 2734 13 = 6 ∧ acceleratedOrbit 13 2734 = 244 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2734 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2734) = 3 ^ 6 * m + 244 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2734.1, data_13_2734.2]

/-- Complete interval computation for depth 13, residue 2735. -/
theorem bounds_13_2735 : exactInterval 13 2735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2735 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2735) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2735 : oddCount 2735 13 = 7 ∧ acceleratedOrbit 13 2735 = 731 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2735 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2735) = 3 ^ 7 * m + 731 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2735.1, data_13_2735.2]

/-- Complete interval computation for depth 13, residue 2736. -/
theorem bounds_13_2736 : exactInterval 13 2736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2736 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2736) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2736 : oddCount 2736 13 = 5 ∧ acceleratedOrbit 13 2736 = 82 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2736 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2736) = 3 ^ 5 * m + 82 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2736.1, data_13_2736.2]

/-- Complete interval computation for depth 13, residue 2737. -/
theorem bounds_13_2737 : exactInterval 13 2737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2737 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2737) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2737 : oddCount 2737 13 = 6 ∧ acceleratedOrbit 13 2737 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2737 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2737) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2737.1, data_13_2737.2]

/-- Complete interval computation for depth 13, residue 2738. -/
theorem bounds_13_2738 : exactInterval 13 2738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_2738 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 2738) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_2738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_2738 : oddCount 2738 13 = 6 ∧ acceleratedOrbit 13 2738 = 245 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_2738 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 2738) = 3 ^ 6 * m + 245 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_2738.1, data_13_2738.2]

end Collatz.Research.StoppingAtlas.Batch0645
