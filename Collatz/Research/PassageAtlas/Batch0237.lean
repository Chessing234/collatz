import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0237

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 7733. -/
theorem bounds_15_7733 : exactInterval 15 7733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7733 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7733) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7733 : oddCount 7733 15 = 4 ∧ acceleratedOrbit 15 7733 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7733 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7733) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7733.1, data_15_7733.2]

/-- Complete interval computation for depth 15, residue 7734. -/
theorem bounds_15_7734 : exactInterval 15 7734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7734 : oddCount 7734 15 = 10 ∧ acceleratedOrbit 15 7734 = 13942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7734) = 3 ^ 10 * m + 13942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7734.1, data_15_7734.2]

/-- Complete interval computation for depth 15, residue 7735. -/
theorem bounds_15_7735 : exactInterval 15 7735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7735 : oddCount 7735 15 = 10 ∧ acceleratedOrbit 15 7735 = 13942 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7735) = 3 ^ 10 * m + 13942 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7735.1, data_15_7735.2]

/-- Complete interval computation for depth 15, residue 7736. -/
theorem bounds_15_7736 : exactInterval 15 7736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7736 : oddCount 7736 15 = 8 ∧ acceleratedOrbit 15 7736 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7736) = 3 ^ 8 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7736.1, data_15_7736.2]

/-- Complete interval computation for depth 15, residue 7737. -/
theorem bounds_15_7737 : exactInterval 15 7737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7737 : oddCount 7737 15 = 8 ∧ acceleratedOrbit 15 7737 = 1550 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7737) = 3 ^ 8 * m + 1550 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7737.1, data_15_7737.2]

/-- Complete interval computation for depth 15, residue 7738. -/
theorem bounds_15_7738 : exactInterval 15 7738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7738 : oddCount 7738 15 = 8 ∧ acceleratedOrbit 15 7738 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7738) = 3 ^ 8 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7738.1, data_15_7738.2]

/-- Complete interval computation for depth 15, residue 7739. -/
theorem bounds_15_7739 : exactInterval 15 7739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7739 : oddCount 7739 15 = 7 ∧ acceleratedOrbit 15 7739 = 517 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7739) = 3 ^ 7 * m + 517 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7739.1, data_15_7739.2]

/-- Complete interval computation for depth 15, residue 7740. -/
theorem bounds_15_7740 : exactInterval 15 7740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7740 : oddCount 7740 15 = 8 ∧ acceleratedOrbit 15 7740 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7740) = 3 ^ 8 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7740.1, data_15_7740.2]

/-- Complete interval computation for depth 15, residue 7741. -/
theorem bounds_15_7741 : exactInterval 15 7741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7741 : oddCount 7741 15 = 8 ∧ acceleratedOrbit 15 7741 = 1552 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7741) = 3 ^ 8 * m + 1552 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7741.1, data_15_7741.2]

/-- Complete interval computation for depth 15, residue 7742. -/
theorem bounds_15_7742 : exactInterval 15 7742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7742 : oddCount 7742 15 = 10 ∧ acceleratedOrbit 15 7742 = 13958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7742) = 3 ^ 10 * m + 13958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7742.1, data_15_7742.2]

/-- Complete interval computation for depth 15, residue 7743. -/
theorem bounds_15_7743 : exactInterval 15 7743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7743 : oddCount 7743 15 = 10 ∧ acceleratedOrbit 15 7743 = 13958 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7743) = 3 ^ 10 * m + 13958 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7743.1, data_15_7743.2]

/-- Complete interval computation for depth 15, residue 7744. -/
theorem bounds_15_7744 : exactInterval 15 7744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7744 : oddCount 7744 15 = 6 ∧ acceleratedOrbit 15 7744 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7744) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7744.1, data_15_7744.2]

/-- Complete interval computation for depth 15, residue 7745. -/
theorem bounds_15_7745 : exactInterval 15 7745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7745 : oddCount 7745 15 = 6 ∧ acceleratedOrbit 15 7745 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7745) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7745.1, data_15_7745.2]

/-- Complete interval computation for depth 15, residue 7746. -/
theorem bounds_15_7746 : exactInterval 15 7746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7746 : oddCount 7746 15 = 6 ∧ acceleratedOrbit 15 7746 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7746) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7746.1, data_15_7746.2]

/-- Complete interval computation for depth 15, residue 7747. -/
theorem bounds_15_7747 : exactInterval 15 7747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7747 : oddCount 7747 15 = 6 ∧ acceleratedOrbit 15 7747 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7747) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7747.1, data_15_7747.2]

/-- Complete interval computation for depth 15, residue 7748. -/
theorem bounds_15_7748 : exactInterval 15 7748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7748 : oddCount 7748 15 = 6 ∧ acceleratedOrbit 15 7748 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7748) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7748.1, data_15_7748.2]

/-- Complete interval computation for depth 15, residue 7749. -/
theorem bounds_15_7749 : exactInterval 15 7749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7749 : oddCount 7749 15 = 6 ∧ acceleratedOrbit 15 7749 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7749) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7749.1, data_15_7749.2]

/-- Complete interval computation for depth 15, residue 7750. -/
theorem bounds_15_7750 : exactInterval 15 7750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7750 : oddCount 7750 15 = 6 ∧ acceleratedOrbit 15 7750 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7750) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7750.1, data_15_7750.2]

/-- Complete interval computation for depth 15, residue 7751. -/
theorem bounds_15_7751 : exactInterval 15 7751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7751 : oddCount 7751 15 = 10 ∧ acceleratedOrbit 15 7751 = 13972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7751) = 3 ^ 10 * m + 13972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7751.1, data_15_7751.2]

/-- Complete interval computation for depth 15, residue 7752. -/
theorem bounds_15_7752 : exactInterval 15 7752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7752 : oddCount 7752 15 = 6 ∧ acceleratedOrbit 15 7752 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7752) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7752.1, data_15_7752.2]

/-- Complete interval computation for depth 15, residue 7753. -/
theorem bounds_15_7753 : exactInterval 15 7753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7753 : oddCount 7753 15 = 8 ∧ acceleratedOrbit 15 7753 = 1553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7753) = 3 ^ 8 * m + 1553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7753.1, data_15_7753.2]

/-- Complete interval computation for depth 15, residue 7754. -/
theorem bounds_15_7754 : exactInterval 15 7754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7754 : oddCount 7754 15 = 6 ∧ acceleratedOrbit 15 7754 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7754) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7754.1, data_15_7754.2]

/-- Complete interval computation for depth 15, residue 7755. -/
theorem bounds_15_7755 : exactInterval 15 7755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7755 : oddCount 7755 15 = 6 ∧ acceleratedOrbit 15 7755 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7755) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7755.1, data_15_7755.2]

/-- Complete interval computation for depth 15, residue 7756. -/
theorem bounds_15_7756 : exactInterval 15 7756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7756 : oddCount 7756 15 = 6 ∧ acceleratedOrbit 15 7756 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7756) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7756.1, data_15_7756.2]

/-- Complete interval computation for depth 15, residue 7757. -/
theorem bounds_15_7757 : exactInterval 15 7757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7757 : oddCount 7757 15 = 6 ∧ acceleratedOrbit 15 7757 = 173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7757) = 3 ^ 6 * m + 173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7757.1, data_15_7757.2]

/-- Complete interval computation for depth 15, residue 7758. -/
theorem bounds_15_7758 : exactInterval 15 7758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7758 : oddCount 7758 15 = 7 ∧ acceleratedOrbit 15 7758 = 518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7758) = 3 ^ 7 * m + 518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7758.1, data_15_7758.2]

/-- Complete interval computation for depth 15, residue 7759. -/
theorem bounds_15_7759 : exactInterval 15 7759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7759 : oddCount 7759 15 = 7 ∧ acceleratedOrbit 15 7759 = 518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7759) = 3 ^ 7 * m + 518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7759.1, data_15_7759.2]

/-- Complete interval computation for depth 15, residue 7760. -/
theorem bounds_15_7760 : exactInterval 15 7760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7760 : oddCount 7760 15 = 6 ∧ acceleratedOrbit 15 7760 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7760) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7760.1, data_15_7760.2]

/-- Complete interval computation for depth 15, residue 7761. -/
theorem bounds_15_7761 : exactInterval 15 7761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7761 : oddCount 7761 15 = 8 ∧ acceleratedOrbit 15 7761 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7761) = 3 ^ 8 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7761.1, data_15_7761.2]

/-- Complete interval computation for depth 15, residue 7762. -/
theorem bounds_15_7762 : exactInterval 15 7762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7762 : oddCount 7762 15 = 8 ∧ acceleratedOrbit 15 7762 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7762) = 3 ^ 8 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7762.1, data_15_7762.2]

/-- Complete interval computation for depth 15, residue 7763. -/
theorem bounds_15_7763 : exactInterval 15 7763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7763 : oddCount 7763 15 = 8 ∧ acceleratedOrbit 15 7763 = 1556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7763) = 3 ^ 8 * m + 1556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7763.1, data_15_7763.2]

/-- Complete interval computation for depth 15, residue 7764. -/
theorem bounds_15_7764 : exactInterval 15 7764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7764 : oddCount 7764 15 = 6 ∧ acceleratedOrbit 15 7764 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7764) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7764.1, data_15_7764.2]

/-- Complete interval computation for depth 15, residue 7765. -/
theorem bounds_15_7765 : exactInterval 15 7765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_7765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 7765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_7765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_7765 : oddCount 7765 15 = 6 ∧ acceleratedOrbit 15 7765 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_7765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 7765) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_7765.1, data_15_7765.2]

end Collatz.Research.PassageAtlas.Batch0237
