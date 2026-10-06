import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0971

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7731. -/
theorem bounds_13_7731 : exactInterval 13 7731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7731 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7731) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7731 : oddCount 7731 13 = 8 ∧ acceleratedOrbit 13 7731 = 6196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7731 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7731) = 3 ^ 8 * m + 6196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7731.1, data_13_7731.2]

/-- Complete interval computation for depth 13, residue 7732. -/
theorem bounds_13_7732 : exactInterval 13 7732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7732 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7732) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7732 : oddCount 7732 13 = 3 ∧ acceleratedOrbit 13 7732 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7732 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7732) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7732.1, data_13_7732.2]

/-- Complete interval computation for depth 13, residue 7733. -/
theorem bounds_13_7733 : exactInterval 13 7733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7733 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7733) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7733 : oddCount 7733 13 = 3 ∧ acceleratedOrbit 13 7733 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7733 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7733) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7733.1, data_13_7733.2]

/-- Complete interval computation for depth 13, residue 7734. -/
theorem bounds_13_7734 : exactInterval 13 7734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7734 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7734) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7734 : oddCount 7734 13 = 10 ∧ acceleratedOrbit 13 7734 = 55768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7734 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7734) = 3 ^ 10 * m + 55768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7734.1, data_13_7734.2]

/-- Complete interval computation for depth 13, residue 7735. -/
theorem bounds_13_7735 : exactInterval 13 7735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7735 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7735) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7735 : oddCount 7735 13 = 10 ∧ acceleratedOrbit 13 7735 = 55768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7735 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7735) = 3 ^ 10 * m + 55768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7735.1, data_13_7735.2]

/-- Complete interval computation for depth 13, residue 7736. -/
theorem bounds_13_7736 : exactInterval 13 7736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7736 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7736) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7736 : oddCount 7736 13 = 7 ∧ acceleratedOrbit 13 7736 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7736 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7736) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7736.1, data_13_7736.2]

/-- Complete interval computation for depth 13, residue 7737. -/
theorem bounds_13_7737 : exactInterval 13 7737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7737 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7737) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7737 : oddCount 7737 13 = 8 ∧ acceleratedOrbit 13 7737 = 6200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7737 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7737) = 3 ^ 8 * m + 6200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7737.1, data_13_7737.2]

/-- Complete interval computation for depth 13, residue 7738. -/
theorem bounds_13_7738 : exactInterval 13 7738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7738 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7738) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7738 : oddCount 7738 13 = 7 ∧ acceleratedOrbit 13 7738 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7738 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7738) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7738.1, data_13_7738.2]

/-- Complete interval computation for depth 13, residue 7739. -/
theorem bounds_13_7739 : exactInterval 13 7739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7739 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7739) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7739 : oddCount 7739 13 = 6 ∧ acceleratedOrbit 13 7739 = 689 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7739 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7739) = 3 ^ 6 * m + 689 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7739.1, data_13_7739.2]

/-- Complete interval computation for depth 13, residue 7740. -/
theorem bounds_13_7740 : exactInterval 13 7740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7740 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7740) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7740 : oddCount 7740 13 = 7 ∧ acceleratedOrbit 13 7740 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7740 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7740) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7740.1, data_13_7740.2]

/-- Complete interval computation for depth 13, residue 7741. -/
theorem bounds_13_7741 : exactInterval 13 7741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7741 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7741) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7741 : oddCount 7741 13 = 7 ∧ acceleratedOrbit 13 7741 = 2069 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7741 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7741) = 3 ^ 7 * m + 2069 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7741.1, data_13_7741.2]

/-- Complete interval computation for depth 13, residue 7742. -/
theorem bounds_13_7742 : exactInterval 13 7742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7742 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7742) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7742 : oddCount 7742 13 = 8 ∧ acceleratedOrbit 13 7742 = 6203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7742 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7742) = 3 ^ 8 * m + 6203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7742.1, data_13_7742.2]

/-- Complete interval computation for depth 13, residue 7743. -/
theorem bounds_13_7743 : exactInterval 13 7743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7743 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7743) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7743 : oddCount 7743 13 = 8 ∧ acceleratedOrbit 13 7743 = 6203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7743 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7743) = 3 ^ 8 * m + 6203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7743.1, data_13_7743.2]

/-- Complete interval computation for depth 13, residue 7744. -/
theorem bounds_13_7744 : exactInterval 13 7744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7744 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7744) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7744 : oddCount 7744 13 = 5 ∧ acceleratedOrbit 13 7744 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7744 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7744) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7744.1, data_13_7744.2]

/-- Complete interval computation for depth 13, residue 7745. -/
theorem bounds_13_7745 : exactInterval 13 7745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7745 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7745) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7745 : oddCount 7745 13 = 5 ∧ acceleratedOrbit 13 7745 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7745 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7745) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7745.1, data_13_7745.2]

end Collatz.Research.StoppingAtlas.Batch0971
