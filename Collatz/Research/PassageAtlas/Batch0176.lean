import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0176

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 5734. -/
theorem bounds_15_5734 : exactInterval 15 5734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5734 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5734) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5734 : oddCount 5734 15 = 6 ∧ acceleratedOrbit 15 5734 = 128 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5734 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5734) = 3 ^ 6 * m + 128 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5734.1, data_15_5734.2]

/-- Complete interval computation for depth 15, residue 5735. -/
theorem bounds_15_5735 : exactInterval 15 5735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5735 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5735) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5735 : oddCount 5735 15 = 11 ∧ acceleratedOrbit 15 5735 = 31013 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5735 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5735) = 3 ^ 11 * m + 31013 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5735.1, data_15_5735.2]

/-- Complete interval computation for depth 15, residue 5736. -/
theorem bounds_15_5736 : exactInterval 15 5736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5736 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5736) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5736 : oddCount 5736 15 = 5 ∧ acceleratedOrbit 15 5736 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5736 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5736) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5736.1, data_15_5736.2]

/-- Complete interval computation for depth 15, residue 5737. -/
theorem bounds_15_5737 : exactInterval 15 5737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5737 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5737) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5737 : oddCount 5737 15 = 10 ∧ acceleratedOrbit 15 5737 = 10343 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5737 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5737) = 3 ^ 10 * m + 10343 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5737.1, data_15_5737.2]

/-- Complete interval computation for depth 15, residue 5738. -/
theorem bounds_15_5738 : exactInterval 15 5738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5738 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5738) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5738 : oddCount 5738 15 = 5 ∧ acceleratedOrbit 15 5738 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5738 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5738) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5738.1, data_15_5738.2]

/-- Complete interval computation for depth 15, residue 5739. -/
theorem bounds_15_5739 : exactInterval 15 5739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5739 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5739) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5739 : oddCount 5739 15 = 9 ∧ acceleratedOrbit 15 5739 = 3449 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5739 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5739) = 3 ^ 9 * m + 3449 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5739.1, data_15_5739.2]

/-- Complete interval computation for depth 15, residue 5740. -/
theorem bounds_15_5740 : exactInterval 15 5740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5740 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5740) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5740 : oddCount 5740 15 = 8 ∧ acceleratedOrbit 15 5740 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5740 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5740) = 3 ^ 8 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5740.1, data_15_5740.2]

/-- Complete interval computation for depth 15, residue 5741. -/
theorem bounds_15_5741 : exactInterval 15 5741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5741 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5741) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5741 : oddCount 5741 15 = 8 ∧ acceleratedOrbit 15 5741 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5741 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5741) = 3 ^ 8 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5741.1, data_15_5741.2]

/-- Complete interval computation for depth 15, residue 5742. -/
theorem bounds_15_5742 : exactInterval 15 5742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5742 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5742) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5742 : oddCount 5742 15 = 8 ∧ acceleratedOrbit 15 5742 = 1151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5742 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5742) = 3 ^ 8 * m + 1151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5742.1, data_15_5742.2]

/-- Complete interval computation for depth 15, residue 5743. -/
theorem bounds_15_5743 : exactInterval 15 5743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5743 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5743) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5743 : oddCount 5743 15 = 9 ∧ acceleratedOrbit 15 5743 = 3451 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5743 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5743) = 3 ^ 9 * m + 3451 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5743.1, data_15_5743.2]

/-- Complete interval computation for depth 15, residue 5744. -/
theorem bounds_15_5744 : exactInterval 15 5744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5744 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5744) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5744 : oddCount 5744 15 = 8 ∧ acceleratedOrbit 15 5744 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5744 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5744) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5744.1, data_15_5744.2]

/-- Complete interval computation for depth 15, residue 5745. -/
theorem bounds_15_5745 : exactInterval 15 5745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5745 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5745) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5745 : oddCount 5745 15 = 5 ∧ acceleratedOrbit 15 5745 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5745 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5745) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5745.1, data_15_5745.2]

/-- Complete interval computation for depth 15, residue 5746. -/
theorem bounds_15_5746 : exactInterval 15 5746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5746 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5746) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5746 : oddCount 5746 15 = 10 ∧ acceleratedOrbit 15 5746 = 10367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5746 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5746) = 3 ^ 10 * m + 10367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5746.1, data_15_5746.2]

/-- Complete interval computation for depth 15, residue 5747. -/
theorem bounds_15_5747 : exactInterval 15 5747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5747 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5747) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5747 : oddCount 5747 15 = 10 ∧ acceleratedOrbit 15 5747 = 10367 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5747 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5747) = 3 ^ 10 * m + 10367 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5747.1, data_15_5747.2]

/-- Complete interval computation for depth 15, residue 5748. -/
theorem bounds_15_5748 : exactInterval 15 5748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5748 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5748) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5748 : oddCount 5748 15 = 8 ∧ acceleratedOrbit 15 5748 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5748 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5748) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5748.1, data_15_5748.2]

/-- Complete interval computation for depth 15, residue 5749. -/
theorem bounds_15_5749 : exactInterval 15 5749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5749 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5749) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5749 : oddCount 5749 15 = 8 ∧ acceleratedOrbit 15 5749 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5749 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5749) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5749.1, data_15_5749.2]

/-- Complete interval computation for depth 15, residue 5750. -/
theorem bounds_15_5750 : exactInterval 15 5750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5750 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5750) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5750 : oddCount 5750 15 = 8 ∧ acceleratedOrbit 15 5750 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5750 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5750) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5750.1, data_15_5750.2]

/-- Complete interval computation for depth 15, residue 5751. -/
theorem bounds_15_5751 : exactInterval 15 5751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5751 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5751) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5751 : oddCount 5751 15 = 8 ∧ acceleratedOrbit 15 5751 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5751 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5751) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5751.1, data_15_5751.2]

/-- Complete interval computation for depth 15, residue 5752. -/
theorem bounds_15_5752 : exactInterval 15 5752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5752 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5752) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5752 : oddCount 5752 15 = 8 ∧ acceleratedOrbit 15 5752 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5752 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5752) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5752.1, data_15_5752.2]

/-- Complete interval computation for depth 15, residue 5753. -/
theorem bounds_15_5753 : exactInterval 15 5753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5753 : oddCount 5753 15 = 9 ∧ acceleratedOrbit 15 5753 = 3458 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5753) = 3 ^ 9 * m + 3458 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5753.1, data_15_5753.2]

/-- Complete interval computation for depth 15, residue 5754. -/
theorem bounds_15_5754 : exactInterval 15 5754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5754 : oddCount 5754 15 = 8 ∧ acceleratedOrbit 15 5754 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5754) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5754.1, data_15_5754.2]

/-- Complete interval computation for depth 15, residue 5755. -/
theorem bounds_15_5755 : exactInterval 15 5755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5755 : oddCount 5755 15 = 8 ∧ acceleratedOrbit 15 5755 = 1154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5755) = 3 ^ 8 * m + 1154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5755.1, data_15_5755.2]

/-- Complete interval computation for depth 15, residue 5756. -/
theorem bounds_15_5756 : exactInterval 15 5756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5756 : oddCount 5756 15 = 10 ∧ acceleratedOrbit 15 5756 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5756) = 3 ^ 10 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5756.1, data_15_5756.2]

/-- Complete interval computation for depth 15, residue 5757. -/
theorem bounds_15_5757 : exactInterval 15 5757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5757 : oddCount 5757 15 = 10 ∧ acceleratedOrbit 15 5757 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5757) = 3 ^ 10 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5757.1, data_15_5757.2]

/-- Complete interval computation for depth 15, residue 5758. -/
theorem bounds_15_5758 : exactInterval 15 5758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5758 : oddCount 5758 15 = 10 ∧ acceleratedOrbit 15 5758 = 10381 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5758) = 3 ^ 10 * m + 10381 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5758.1, data_15_5758.2]

/-- Complete interval computation for depth 15, residue 5759. -/
theorem bounds_15_5759 : exactInterval 15 5759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5759 : oddCount 5759 15 = 12 ∧ acceleratedOrbit 15 5759 = 93419 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5759) = 3 ^ 12 * m + 93419 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5759.1, data_15_5759.2]

/-- Complete interval computation for depth 15, residue 5760. -/
theorem bounds_15_5760 : exactInterval 15 5760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5760 : oddCount 5760 15 = 3 ∧ acceleratedOrbit 15 5760 = 5 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5760) = 3 ^ 3 * m + 5 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5760.1, data_15_5760.2]

/-- Complete interval computation for depth 15, residue 5761. -/
theorem bounds_15_5761 : exactInterval 15 5761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5761 : oddCount 5761 15 = 10 ∧ acceleratedOrbit 15 5761 = 10388 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5761) = 3 ^ 10 * m + 10388 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5761.1, data_15_5761.2]

/-- Complete interval computation for depth 15, residue 5762. -/
theorem bounds_15_5762 : exactInterval 15 5762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5762 : oddCount 5762 15 = 5 ∧ acceleratedOrbit 15 5762 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5762) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5762.1, data_15_5762.2]

/-- Complete interval computation for depth 15, residue 5763. -/
theorem bounds_15_5763 : exactInterval 15 5763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5763 : oddCount 5763 15 = 5 ∧ acceleratedOrbit 15 5763 = 44 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5763) = 3 ^ 5 * m + 44 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5763.1, data_15_5763.2]

/-- Complete interval computation for depth 15, residue 5764. -/
theorem bounds_15_5764 : exactInterval 15 5764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5764 : oddCount 5764 15 = 7 ∧ acceleratedOrbit 15 5764 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5764) = 3 ^ 7 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5764.1, data_15_5764.2]

/-- Complete interval computation for depth 15, residue 5765. -/
theorem bounds_15_5765 : exactInterval 15 5765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5765 : oddCount 5765 15 = 7 ∧ acceleratedOrbit 15 5765 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5765) = 3 ^ 7 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5765.1, data_15_5765.2]

/-- Complete interval computation for depth 15, residue 5766. -/
theorem bounds_15_5766 : exactInterval 15 5766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_5766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 5766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_5766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_5766 : oddCount 5766 15 = 7 ∧ acceleratedOrbit 15 5766 = 386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_5766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 5766) = 3 ^ 7 * m + 386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_5766.1, data_15_5766.2]

end Collatz.Research.PassageAtlas.Batch0176
