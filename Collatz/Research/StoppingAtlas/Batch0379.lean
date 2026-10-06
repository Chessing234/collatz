import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0379

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 2734. -/
theorem bounds_12_2734 : exactInterval 12 2734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2734 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2734) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2734 : oddCount 2734 12 = 6 ∧ acceleratedOrbit 12 2734 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2734 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2734) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2734.1, data_12_2734.2]

/-- Complete interval computation for depth 12, residue 2735. -/
theorem bounds_12_2735 : exactInterval 12 2735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2735 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2735) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2735 : oddCount 2735 12 = 6 ∧ acceleratedOrbit 12 2735 = 487 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2735 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2735) = 3 ^ 6 * m + 487 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2735.1, data_12_2735.2]

/-- Complete interval computation for depth 12, residue 2736. -/
theorem bounds_12_2736 : exactInterval 12 2736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2736 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2736) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2736 : oddCount 2736 12 = 5 ∧ acceleratedOrbit 12 2736 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2736 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2736) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2736.1, data_12_2736.2]

/-- Complete interval computation for depth 12, residue 2737. -/
theorem bounds_12_2737 : exactInterval 12 2737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2737 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2737) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2737 : oddCount 2737 12 = 5 ∧ acceleratedOrbit 12 2737 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2737 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2737) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2737.1, data_12_2737.2]

/-- Complete interval computation for depth 12, residue 2738. -/
theorem bounds_12_2738 : exactInterval 12 2738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2738 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2738) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2738 : oddCount 2738 12 = 5 ∧ acceleratedOrbit 12 2738 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2738 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2738) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2738.1, data_12_2738.2]

/-- Complete interval computation for depth 12, residue 2739. -/
theorem bounds_12_2739 : exactInterval 12 2739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2739 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2739) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2739 : oddCount 2739 12 = 5 ∧ acceleratedOrbit 12 2739 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2739 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2739) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2739.1, data_12_2739.2]

/-- Complete interval computation for depth 12, residue 2740. -/
theorem bounds_12_2740 : exactInterval 12 2740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2740 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2740) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2740 : oddCount 2740 12 = 5 ∧ acceleratedOrbit 12 2740 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2740 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2740) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2740.1, data_12_2740.2]

/-- Complete interval computation for depth 12, residue 2741. -/
theorem bounds_12_2741 : exactInterval 12 2741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2741 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2741) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2741 : oddCount 2741 12 = 5 ∧ acceleratedOrbit 12 2741 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2741 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2741) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2741.1, data_12_2741.2]

/-- Complete interval computation for depth 12, residue 2742. -/
theorem bounds_12_2742 : exactInterval 12 2742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2742 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2742) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2742 : oddCount 2742 12 = 7 ∧ acceleratedOrbit 12 2742 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2742 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2742) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2742.1, data_12_2742.2]

/-- Complete interval computation for depth 12, residue 2743. -/
theorem bounds_12_2743 : exactInterval 12 2743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2743 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2743) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2743 : oddCount 2743 12 = 7 ∧ acceleratedOrbit 12 2743 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2743 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2743) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2743.1, data_12_2743.2]

/-- Complete interval computation for depth 12, residue 2744. -/
theorem bounds_12_2744 : exactInterval 12 2744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2744 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2744) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2744 : oddCount 2744 12 = 5 ∧ acceleratedOrbit 12 2744 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2744 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2744) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2744.1, data_12_2744.2]

/-- Complete interval computation for depth 12, residue 2745. -/
theorem bounds_12_2745 : exactInterval 12 2745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2745 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2745) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2745 : oddCount 2745 12 = 5 ∧ acceleratedOrbit 12 2745 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2745 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2745) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2745.1, data_12_2745.2]

/-- Complete interval computation for depth 12, residue 2746. -/
theorem bounds_12_2746 : exactInterval 12 2746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2746 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2746) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2746 : oddCount 2746 12 = 5 ∧ acceleratedOrbit 12 2746 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2746 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2746) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2746.1, data_12_2746.2]

/-- Complete interval computation for depth 12, residue 2747. -/
theorem bounds_12_2747 : exactInterval 12 2747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2747 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2747) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2747 : oddCount 2747 12 = 7 ∧ acceleratedOrbit 12 2747 = 1468 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2747 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2747) = 3 ^ 7 * m + 1468 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2747.1, data_12_2747.2]

/-- Complete interval computation for depth 12, residue 2748. -/
theorem bounds_12_2748 : exactInterval 12 2748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_2748 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 2748) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_2748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_2748 : oddCount 2748 12 = 6 ∧ acceleratedOrbit 12 2748 = 490 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_2748 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 2748) = 3 ^ 6 * m + 490 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_2748.1, data_12_2748.2]

end Collatz.Research.StoppingAtlas.Batch0379
