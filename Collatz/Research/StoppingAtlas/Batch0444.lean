import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0444

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3732. -/
theorem bounds_12_3732 : exactInterval 12 3732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3732 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3732) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3732 : oddCount 3732 12 = 6 ∧ acceleratedOrbit 12 3732 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3732 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3732) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3732.1, data_12_3732.2]

/-- Complete interval computation for depth 12, residue 3733. -/
theorem bounds_12_3733 : exactInterval 12 3733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3733 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3733) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3733 : oddCount 3733 12 = 6 ∧ acceleratedOrbit 12 3733 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3733 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3733) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3733.1, data_12_3733.2]

/-- Complete interval computation for depth 12, residue 3734. -/
theorem bounds_12_3734 : exactInterval 12 3734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3734 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3734) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3734 : oddCount 3734 12 = 4 ∧ acceleratedOrbit 12 3734 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3734 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3734) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3734.1, data_12_3734.2]

/-- Complete interval computation for depth 12, residue 3735. -/
theorem bounds_12_3735 : exactInterval 12 3735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3735 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3735) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3735 : oddCount 3735 12 = 4 ∧ acceleratedOrbit 12 3735 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3735 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3735) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3735.1, data_12_3735.2]

/-- Complete interval computation for depth 12, residue 3736. -/
theorem bounds_12_3736 : exactInterval 12 3736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3736 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3736) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3736 : oddCount 3736 12 = 6 ∧ acceleratedOrbit 12 3736 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3736 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3736) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3736.1, data_12_3736.2]

/-- Complete interval computation for depth 12, residue 3737. -/
theorem bounds_12_3737 : exactInterval 12 3737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3737 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3737) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3737 : oddCount 3737 12 = 8 ∧ acceleratedOrbit 12 3737 = 5993 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3737 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3737) = 3 ^ 8 * m + 5993 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3737.1, data_12_3737.2]

/-- Complete interval computation for depth 12, residue 3738. -/
theorem bounds_12_3738 : exactInterval 12 3738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3738 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3738) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3738 : oddCount 3738 12 = 6 ∧ acceleratedOrbit 12 3738 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3738 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3738) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3738.1, data_12_3738.2]

/-- Complete interval computation for depth 12, residue 3739. -/
theorem bounds_12_3739 : exactInterval 12 3739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3739 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3739) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3739 : oddCount 3739 12 = 9 ∧ acceleratedOrbit 12 3739 = 17975 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3739 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3739) = 3 ^ 9 * m + 17975 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3739.1, data_12_3739.2]

/-- Complete interval computation for depth 12, residue 3740. -/
theorem bounds_12_3740 : exactInterval 12 3740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3740 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3740) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3740 : oddCount 3740 12 = 7 ∧ acceleratedOrbit 12 3740 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3740 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3740) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3740.1, data_12_3740.2]

/-- Complete interval computation for depth 12, residue 3741. -/
theorem bounds_12_3741 : exactInterval 12 3741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3741 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3741) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3741 : oddCount 3741 12 = 7 ∧ acceleratedOrbit 12 3741 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3741 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3741) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3741.1, data_12_3741.2]

/-- Complete interval computation for depth 12, residue 3742. -/
theorem bounds_12_3742 : exactInterval 12 3742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3742 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3742) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3742 : oddCount 3742 12 = 7 ∧ acceleratedOrbit 12 3742 = 2000 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3742 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3742) = 3 ^ 7 * m + 2000 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3742.1, data_12_3742.2]

/-- Complete interval computation for depth 12, residue 3743. -/
theorem bounds_12_3743 : exactInterval 12 3743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3743 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3743) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3743 : oddCount 3743 12 = 9 ∧ acceleratedOrbit 12 3743 = 17992 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3743 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3743) = 3 ^ 9 * m + 17992 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3743.1, data_12_3743.2]

/-- Complete interval computation for depth 12, residue 3744. -/
theorem bounds_12_3744 : exactInterval 12 3744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3744 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3744) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3744 : oddCount 3744 12 = 3 ∧ acceleratedOrbit 12 3744 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3744 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3744) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3744.1, data_12_3744.2]

/-- Complete interval computation for depth 12, residue 3745. -/
theorem bounds_12_3745 : exactInterval 12 3745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3745 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3745) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3745 : oddCount 3745 12 = 6 ∧ acceleratedOrbit 12 3745 = 667 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3745 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3745) = 3 ^ 6 * m + 667 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3745.1, data_12_3745.2]

/-- Complete interval computation for depth 12, residue 3746. -/
theorem bounds_12_3746 : exactInterval 12 3746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3746 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3746) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3746 : oddCount 3746 12 = 6 ∧ acceleratedOrbit 12 3746 = 668 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3746 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3746) = 3 ^ 6 * m + 668 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3746.1, data_12_3746.2]

end Collatz.Research.StoppingAtlas.Batch0444
