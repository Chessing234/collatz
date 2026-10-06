import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0580

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1725. -/
theorem bounds_13_1725 : exactInterval 13 1725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1725 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1725) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1725 : oddCount 1725 13 = 6 ∧ acceleratedOrbit 13 1725 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1725 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1725) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1725.1, data_13_1725.2]

/-- Complete interval computation for depth 13, residue 1726. -/
theorem bounds_13_1726 : exactInterval 13 1726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1726 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1726) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1726 : oddCount 1726 13 = 6 ∧ acceleratedOrbit 13 1726 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1726 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1726) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1726.1, data_13_1726.2]

/-- Complete interval computation for depth 13, residue 1727. -/
theorem bounds_13_1727 : exactInterval 13 1727 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1727 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1727) 13 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1727 : oddCount 1727 13 = 8 ∧ acceleratedOrbit 13 1727 = 1384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1727 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1727) = 3 ^ 8 * m + 1384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1727.1, data_13_1727.2]

/-- Complete interval computation for depth 13, residue 1728. -/
theorem bounds_13_1728 : exactInterval 13 1728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1728 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1728) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1728 : oddCount 1728 13 = 6 ∧ acceleratedOrbit 13 1728 = 161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1728 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1728) = 3 ^ 6 * m + 161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1728.1, data_13_1728.2]

/-- Complete interval computation for depth 13, residue 1729. -/
theorem bounds_13_1729 : exactInterval 13 1729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1729 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1729) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1729 : oddCount 1729 13 = 6 ∧ acceleratedOrbit 13 1729 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1729 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1729) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1729.1, data_13_1729.2]

/-- Complete interval computation for depth 13, residue 1730. -/
theorem bounds_13_1730 : exactInterval 13 1730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1730 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1730) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1730 : oddCount 1730 13 = 8 ∧ acceleratedOrbit 13 1730 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1730 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1730) = 3 ^ 8 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1730.1, data_13_1730.2]

/-- Complete interval computation for depth 13, residue 1731. -/
theorem bounds_13_1731 : exactInterval 13 1731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1731 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1731) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1731 : oddCount 1731 13 = 8 ∧ acceleratedOrbit 13 1731 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1731 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1731) = 3 ^ 8 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1731.1, data_13_1731.2]

/-- Complete interval computation for depth 13, residue 1732. -/
theorem bounds_13_1732 : exactInterval 13 1732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1732 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1732) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1732 : oddCount 1732 13 = 5 ∧ acceleratedOrbit 13 1732 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1732 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1732) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1732.1, data_13_1732.2]

/-- Complete interval computation for depth 13, residue 1733. -/
theorem bounds_13_1733 : exactInterval 13 1733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1733 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1733) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1733 : oddCount 1733 13 = 5 ∧ acceleratedOrbit 13 1733 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1733 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1733) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1733.1, data_13_1733.2]

/-- Complete interval computation for depth 13, residue 1734. -/
theorem bounds_13_1734 : exactInterval 13 1734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1734 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1734) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1734 : oddCount 1734 13 = 5 ∧ acceleratedOrbit 13 1734 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1734 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1734) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1734.1, data_13_1734.2]

/-- Complete interval computation for depth 13, residue 1735. -/
theorem bounds_13_1735 : exactInterval 13 1735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1735 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1735) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1735 : oddCount 1735 13 = 6 ∧ acceleratedOrbit 13 1735 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1735 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1735) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1735.1, data_13_1735.2]

/-- Complete interval computation for depth 13, residue 1736. -/
theorem bounds_13_1736 : exactInterval 13 1736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1736 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1736) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1736 : oddCount 1736 13 = 5 ∧ acceleratedOrbit 13 1736 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1736 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1736) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1736.1, data_13_1736.2]

/-- Complete interval computation for depth 13, residue 1737. -/
theorem bounds_13_1737 : exactInterval 13 1737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1737 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1737) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1737 : oddCount 1737 13 = 6 ∧ acceleratedOrbit 13 1737 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1737 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1737) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1737.1, data_13_1737.2]

/-- Complete interval computation for depth 13, residue 1738. -/
theorem bounds_13_1738 : exactInterval 13 1738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1738 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1738) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1738 : oddCount 1738 13 = 5 ∧ acceleratedOrbit 13 1738 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1738 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1738) = 3 ^ 5 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1738.1, data_13_1738.2]

/-- Complete interval computation for depth 13, residue 1739. -/
theorem bounds_13_1739 : exactInterval 13 1739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1739 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1739) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1739 : oddCount 1739 13 = 8 ∧ acceleratedOrbit 13 1739 = 1397 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1739 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1739) = 3 ^ 8 * m + 1397 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1739.1, data_13_1739.2]

end Collatz.Research.StoppingAtlas.Batch0580
