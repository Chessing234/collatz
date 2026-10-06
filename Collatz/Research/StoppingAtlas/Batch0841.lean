import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0841

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5734. -/
theorem bounds_13_5734 : exactInterval 13 5734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5734 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5734) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5734 : oddCount 5734 13 = 6 ∧ acceleratedOrbit 13 5734 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5734 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5734) = 3 ^ 6 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5734.1, data_13_5734.2]

/-- Complete interval computation for depth 13, residue 5735. -/
theorem bounds_13_5735 : exactInterval 13 5735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5735 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5735) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5735 : oddCount 5735 13 = 9 ∧ acceleratedOrbit 13 5735 = 13783 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5735 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5735) = 3 ^ 9 * m + 13783 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5735.1, data_13_5735.2]

/-- Complete interval computation for depth 13, residue 5736. -/
theorem bounds_13_5736 : exactInterval 13 5736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5736 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5736) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5736 : oddCount 5736 13 = 3 ∧ acceleratedOrbit 13 5736 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5736 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5736) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5736.1, data_13_5736.2]

/-- Complete interval computation for depth 13, residue 5737. -/
theorem bounds_13_5737 : exactInterval 13 5737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5737 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5737) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5737 : oddCount 5737 13 = 9 ∧ acceleratedOrbit 13 5737 = 13790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5737 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5737) = 3 ^ 9 * m + 13790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5737.1, data_13_5737.2]

/-- Complete interval computation for depth 13, residue 5738. -/
theorem bounds_13_5738 : exactInterval 13 5738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5738 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5738) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5738 : oddCount 5738 13 = 3 ∧ acceleratedOrbit 13 5738 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5738 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5738) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5738.1, data_13_5738.2]

/-- Complete interval computation for depth 13, residue 5739. -/
theorem bounds_13_5739 : exactInterval 13 5739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5739 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5739) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5739 : oddCount 5739 13 = 9 ∧ acceleratedOrbit 13 5739 = 13796 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5739 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5739) = 3 ^ 9 * m + 13796 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5739.1, data_13_5739.2]

/-- Complete interval computation for depth 13, residue 5740. -/
theorem bounds_13_5740 : exactInterval 13 5740 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5740 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5740) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5740 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5740 : oddCount 5740 13 = 7 ∧ acceleratedOrbit 13 5740 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5740 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5740) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5740.1, data_13_5740.2]

/-- Complete interval computation for depth 13, residue 5741. -/
theorem bounds_13_5741 : exactInterval 13 5741 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5741 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5741) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5741 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5741 : oddCount 5741 13 = 7 ∧ acceleratedOrbit 13 5741 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5741 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5741) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5741.1, data_13_5741.2]

/-- Complete interval computation for depth 13, residue 5742. -/
theorem bounds_13_5742 : exactInterval 13 5742 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5742 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5742) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5742 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5742 : oddCount 5742 13 = 7 ∧ acceleratedOrbit 13 5742 = 1534 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5742 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5742) = 3 ^ 7 * m + 1534 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5742.1, data_13_5742.2]

/-- Complete interval computation for depth 13, residue 5743. -/
theorem bounds_13_5743 : exactInterval 13 5743 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5743 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5743) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5743 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5743 : oddCount 5743 13 = 8 ∧ acceleratedOrbit 13 5743 = 4601 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5743 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5743) = 3 ^ 8 * m + 4601 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5743.1, data_13_5743.2]

/-- Complete interval computation for depth 13, residue 5744. -/
theorem bounds_13_5744 : exactInterval 13 5744 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5744 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5744) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5744 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5744 : oddCount 5744 13 = 8 ∧ acceleratedOrbit 13 5744 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5744 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5744) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5744.1, data_13_5744.2]

/-- Complete interval computation for depth 13, residue 5745. -/
theorem bounds_13_5745 : exactInterval 13 5745 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5745 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5745) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5745 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5745 : oddCount 5745 13 = 3 ∧ acceleratedOrbit 13 5745 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5745 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5745) = 3 ^ 3 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5745.1, data_13_5745.2]

/-- Complete interval computation for depth 13, residue 5746. -/
theorem bounds_13_5746 : exactInterval 13 5746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5746 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5746) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5746 : oddCount 5746 13 = 8 ∧ acceleratedOrbit 13 5746 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5746 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5746) = 3 ^ 8 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5746.1, data_13_5746.2]

/-- Complete interval computation for depth 13, residue 5747. -/
theorem bounds_13_5747 : exactInterval 13 5747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5747 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5747) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5747 : oddCount 5747 13 = 8 ∧ acceleratedOrbit 13 5747 = 4607 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5747 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5747) = 3 ^ 8 * m + 4607 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5747.1, data_13_5747.2]

/-- Complete interval computation for depth 13, residue 5748. -/
theorem bounds_13_5748 : exactInterval 13 5748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5748 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5748) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5748 : oddCount 5748 13 = 8 ∧ acceleratedOrbit 13 5748 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5748 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5748) = 3 ^ 8 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5748.1, data_13_5748.2]

end Collatz.Research.StoppingAtlas.Batch0841
