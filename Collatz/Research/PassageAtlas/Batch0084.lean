import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0084

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 2719. -/
theorem bounds_15_2719 : exactInterval 15 2719 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2719 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2719) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2719 : oddCount 2719 15 = 9 ∧ acceleratedOrbit 15 2719 = 1634 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2719 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2719) = 3 ^ 9 * m + 1634 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2719.1, data_15_2719.2]

/-- Complete interval computation for depth 15, residue 2720. -/
theorem bounds_15_2720 : exactInterval 15 2720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2720 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2720) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2720 : oddCount 2720 15 = 2 ∧ acceleratedOrbit 15 2720 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2720 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2720) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2720.1, data_15_2720.2]

/-- Complete interval computation for depth 15, residue 2721. -/
theorem bounds_15_2721 : exactInterval 15 2721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2721 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2721) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2721 : oddCount 2721 15 = 9 ∧ acceleratedOrbit 15 2721 = 1637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2721 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2721) = 3 ^ 9 * m + 1637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2721.1, data_15_2721.2]

/-- Complete interval computation for depth 15, residue 2722. -/
theorem bounds_15_2722 : exactInterval 15 2722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2722 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2722) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2722 : oddCount 2722 15 = 9 ∧ acceleratedOrbit 15 2722 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2722 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2722) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2722.1, data_15_2722.2]

/-- Complete interval computation for depth 15, residue 2723. -/
theorem bounds_15_2723 : exactInterval 15 2723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2723 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2723) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2723 : oddCount 2723 15 = 9 ∧ acceleratedOrbit 15 2723 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2723 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2723) = 3 ^ 9 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2723.1, data_15_2723.2]

/-- Complete interval computation for depth 15, residue 2724. -/
theorem bounds_15_2724 : exactInterval 15 2724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2724 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2724) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2724 : oddCount 2724 15 = 11 ∧ acceleratedOrbit 15 2724 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2724 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2724) = 3 ^ 11 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2724.1, data_15_2724.2]

/-- Complete interval computation for depth 15, residue 2725. -/
theorem bounds_15_2725 : exactInterval 15 2725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2725 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2725) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2725 : oddCount 2725 15 = 11 ∧ acceleratedOrbit 15 2725 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2725 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2725) = 3 ^ 11 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2725.1, data_15_2725.2]

/-- Complete interval computation for depth 15, residue 2726. -/
theorem bounds_15_2726 : exactInterval 15 2726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2726 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2726) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2726 : oddCount 2726 15 = 11 ∧ acceleratedOrbit 15 2726 = 14762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2726 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2726) = 3 ^ 11 * m + 14762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2726.1, data_15_2726.2]

/-- Complete interval computation for depth 15, residue 2727. -/
theorem bounds_15_2727 : exactInterval 15 2727 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2727 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2727) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2727 : oddCount 2727 15 = 9 ∧ acceleratedOrbit 15 2727 = 1639 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2727 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2727) = 3 ^ 9 * m + 1639 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2727.1, data_15_2727.2]

/-- Complete interval computation for depth 15, residue 2728. -/
theorem bounds_15_2728 : exactInterval 15 2728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2728 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2728) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2728 : oddCount 2728 15 = 2 ∧ acceleratedOrbit 15 2728 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2728 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2728) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2728.1, data_15_2728.2]

/-- Complete interval computation for depth 15, residue 2729. -/
theorem bounds_15_2729 : exactInterval 15 2729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2729 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2729) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2729 : oddCount 2729 15 = 13 ∧ acceleratedOrbit 15 2729 = 132860 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2729 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2729) = 3 ^ 13 * m + 132860 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2729.1, data_15_2729.2]

/-- Complete interval computation for depth 15, residue 2730. -/
theorem bounds_15_2730 : exactInterval 15 2730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2730 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2730) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2730 : oddCount 2730 15 = 2 ∧ acceleratedOrbit 15 2730 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2730 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2730) = 3 ^ 2 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2730.1, data_15_2730.2]

/-- Complete interval computation for depth 15, residue 2731. -/
theorem bounds_15_2731 : exactInterval 15 2731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2731 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2731) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2731 : oddCount 2731 15 = 8 ∧ acceleratedOrbit 15 2731 = 548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2731 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2731) = 3 ^ 8 * m + 548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2731.1, data_15_2731.2]

/-- Complete interval computation for depth 15, residue 2732. -/
theorem bounds_15_2732 : exactInterval 15 2732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2732 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2732) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2732 : oddCount 2732 15 = 6 ∧ acceleratedOrbit 15 2732 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2732 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2732) = 3 ^ 6 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2732.1, data_15_2732.2]

/-- Complete interval computation for depth 15, residue 2733. -/
theorem bounds_15_2733 : exactInterval 15 2733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2733 : oddCount 2733 15 = 6 ∧ acceleratedOrbit 15 2733 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2733) = 3 ^ 6 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2733.1, data_15_2733.2]

/-- Complete interval computation for depth 15, residue 2734. -/
theorem bounds_15_2734 : exactInterval 15 2734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2734 : oddCount 2734 15 = 6 ∧ acceleratedOrbit 15 2734 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2734) = 3 ^ 6 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2734.1, data_15_2734.2]

/-- Complete interval computation for depth 15, residue 2735. -/
theorem bounds_15_2735 : exactInterval 15 2735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2735 : oddCount 2735 15 = 9 ∧ acceleratedOrbit 15 2735 = 1646 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2735) = 3 ^ 9 * m + 1646 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2735.1, data_15_2735.2]

/-- Complete interval computation for depth 15, residue 2736. -/
theorem bounds_15_2736 : exactInterval 15 2736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2736 : oddCount 2736 15 = 6 ∧ acceleratedOrbit 15 2736 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2736) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2736.1, data_15_2736.2]

/-- Complete interval computation for depth 15, residue 2737. -/
theorem bounds_15_2737 : exactInterval 15 2737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2737 : oddCount 2737 15 = 7 ∧ acceleratedOrbit 15 2737 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2737) = 3 ^ 7 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2737.1, data_15_2737.2]

/-- Complete interval computation for depth 15, residue 2738. -/
theorem bounds_15_2738 : exactInterval 15 2738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2738 : oddCount 2738 15 = 7 ∧ acceleratedOrbit 15 2738 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2738) = 3 ^ 7 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2738.1, data_15_2738.2]

/-- Complete interval computation for depth 15, residue 2739. -/
theorem bounds_15_2739 : exactInterval 15 2739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2739 : oddCount 2739 15 = 7 ∧ acceleratedOrbit 15 2739 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2739) = 3 ^ 7 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2739.1, data_15_2739.2]

/-- Complete interval computation for depth 15, residue 2740. -/
theorem bounds_15_2740 : exactInterval 15 2740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2740 : oddCount 2740 15 = 6 ∧ acceleratedOrbit 15 2740 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2740) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2740.1, data_15_2740.2]

/-- Complete interval computation for depth 15, residue 2741. -/
theorem bounds_15_2741 : exactInterval 15 2741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2741 : oddCount 2741 15 = 6 ∧ acceleratedOrbit 15 2741 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2741) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2741.1, data_15_2741.2]

/-- Complete interval computation for depth 15, residue 2742. -/
theorem bounds_15_2742 : exactInterval 15 2742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2742 : oddCount 2742 15 = 8 ∧ acceleratedOrbit 15 2742 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2742) = 3 ^ 8 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2742.1, data_15_2742.2]

/-- Complete interval computation for depth 15, residue 2743. -/
theorem bounds_15_2743 : exactInterval 15 2743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2743 : oddCount 2743 15 = 8 ∧ acceleratedOrbit 15 2743 = 550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2743) = 3 ^ 8 * m + 550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2743.1, data_15_2743.2]

/-- Complete interval computation for depth 15, residue 2744. -/
theorem bounds_15_2744 : exactInterval 15 2744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2744 : oddCount 2744 15 = 6 ∧ acceleratedOrbit 15 2744 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2744) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2744.1, data_15_2744.2]

/-- Complete interval computation for depth 15, residue 2745. -/
theorem bounds_15_2745 : exactInterval 15 2745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2745 : oddCount 2745 15 = 7 ∧ acceleratedOrbit 15 2745 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2745) = 3 ^ 7 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2745.1, data_15_2745.2]

/-- Complete interval computation for depth 15, residue 2746. -/
theorem bounds_15_2746 : exactInterval 15 2746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2746 : oddCount 2746 15 = 6 ∧ acceleratedOrbit 15 2746 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2746) = 3 ^ 6 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2746.1, data_15_2746.2]

/-- Complete interval computation for depth 15, residue 2747. -/
theorem bounds_15_2747 : exactInterval 15 2747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2747 : oddCount 2747 15 = 8 ∧ acceleratedOrbit 15 2747 = 551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2747) = 3 ^ 8 * m + 551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2747.1, data_15_2747.2]

/-- Complete interval computation for depth 15, residue 2748. -/
theorem bounds_15_2748 : exactInterval 15 2748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2748 : oddCount 2748 15 = 7 ∧ acceleratedOrbit 15 2748 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2748) = 3 ^ 7 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2748.1, data_15_2748.2]

/-- Complete interval computation for depth 15, residue 2749. -/
theorem bounds_15_2749 : exactInterval 15 2749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2749 : oddCount 2749 15 = 7 ∧ acceleratedOrbit 15 2749 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2749) = 3 ^ 7 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2749.1, data_15_2749.2]

/-- Complete interval computation for depth 15, residue 2750. -/
theorem bounds_15_2750 : exactInterval 15 2750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2750 : oddCount 2750 15 = 7 ∧ acceleratedOrbit 15 2750 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2750) = 3 ^ 7 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2750.1, data_15_2750.2]

/-- Complete interval computation for depth 15, residue 2751. -/
theorem bounds_15_2751 : exactInterval 15 2751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_2751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 2751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_2751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_2751 : oddCount 2751 15 = 11 ∧ acceleratedOrbit 15 2751 = 14879 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_2751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 2751) = 3 ^ 11 * m + 14879 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_2751.1, data_15_2751.2]

end Collatz.Research.PassageAtlas.Batch0084
