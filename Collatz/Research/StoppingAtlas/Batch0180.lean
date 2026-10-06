import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0180

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1725. -/
theorem bounds_11_1725 : exactInterval 11 1725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1725 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1725) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1725 : oddCount 1725 11 = 5 ∧ acceleratedOrbit 11 1725 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1725 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1725) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1725.1, data_11_1725.2]

/-- Complete interval computation for depth 11, residue 1726. -/
theorem bounds_11_1726 : exactInterval 11 1726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1726 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1726) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1726 : oddCount 1726 11 = 5 ∧ acceleratedOrbit 11 1726 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1726 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1726) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1726.1, data_11_1726.2]

/-- Complete interval computation for depth 11, residue 1727. -/
theorem bounds_11_1727 : exactInterval 11 1727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1727 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1727) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1727 : oddCount 1727 11 = 8 ∧ acceleratedOrbit 11 1727 = 5536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1727 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1727) = 3 ^ 8 * m + 5536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1727.1, data_11_1727.2]

/-- Complete interval computation for depth 11, residue 1728. -/
theorem bounds_11_1728 : exactInterval 11 1728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1728 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1728) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1728 : oddCount 1728 11 = 4 ∧ acceleratedOrbit 11 1728 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1728 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1728) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1728.1, data_11_1728.2]

/-- Complete interval computation for depth 11, residue 1729. -/
theorem bounds_11_1729 : exactInterval 11 1729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1729 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1729) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1729 : oddCount 1729 11 = 5 ∧ acceleratedOrbit 11 1729 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1729 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1729) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1729.1, data_11_1729.2]

/-- Complete interval computation for depth 11, residue 1730. -/
theorem bounds_11_1730 : exactInterval 11 1730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1730 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1730) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1730 : oddCount 1730 11 = 7 ∧ acceleratedOrbit 11 1730 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1730 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1730) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1730.1, data_11_1730.2]

/-- Complete interval computation for depth 11, residue 1731. -/
theorem bounds_11_1731 : exactInterval 11 1731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1731 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1731) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1731 : oddCount 1731 11 = 7 ∧ acceleratedOrbit 11 1731 = 1853 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1731 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1731) = 3 ^ 7 * m + 1853 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1731.1, data_11_1731.2]

/-- Complete interval computation for depth 11, residue 1732. -/
theorem bounds_11_1732 : exactInterval 11 1732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1732 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1732) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1732 : oddCount 1732 11 = 3 ∧ acceleratedOrbit 11 1732 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1732 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1732) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1732.1, data_11_1732.2]

/-- Complete interval computation for depth 11, residue 1733. -/
theorem bounds_11_1733 : exactInterval 11 1733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1733 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1733) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1733 : oddCount 1733 11 = 3 ∧ acceleratedOrbit 11 1733 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1733 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1733) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1733.1, data_11_1733.2]

/-- Complete interval computation for depth 11, residue 1734. -/
theorem bounds_11_1734 : exactInterval 11 1734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1734 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1734) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1734 : oddCount 1734 11 = 3 ∧ acceleratedOrbit 11 1734 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1734 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1734) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1734.1, data_11_1734.2]

/-- Complete interval computation for depth 11, residue 1735. -/
theorem bounds_11_1735 : exactInterval 11 1735 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1735 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1735) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1735 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1735 : oddCount 1735 11 = 5 ∧ acceleratedOrbit 11 1735 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1735 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1735) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1735.1, data_11_1735.2]

/-- Complete interval computation for depth 11, residue 1736. -/
theorem bounds_11_1736 : exactInterval 11 1736 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1736 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1736) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1736 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1736 : oddCount 1736 11 = 3 ∧ acceleratedOrbit 11 1736 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1736 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1736) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1736.1, data_11_1736.2]

/-- Complete interval computation for depth 11, residue 1737. -/
theorem bounds_11_1737 : exactInterval 11 1737 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1737 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1737) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1737 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1737 : oddCount 1737 11 = 6 ∧ acceleratedOrbit 11 1737 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1737 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1737) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1737.1, data_11_1737.2]

/-- Complete interval computation for depth 11, residue 1738. -/
theorem bounds_11_1738 : exactInterval 11 1738 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1738 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1738) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1738 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1738 : oddCount 1738 11 = 3 ∧ acceleratedOrbit 11 1738 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1738 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1738) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1738.1, data_11_1738.2]

/-- Complete interval computation for depth 11, residue 1739. -/
theorem bounds_11_1739 : exactInterval 11 1739 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1739 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1739) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1739 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1739 : oddCount 1739 11 = 7 ∧ acceleratedOrbit 11 1739 = 1862 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1739 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1739) = 3 ^ 7 * m + 1862 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1739.1, data_11_1739.2]

end Collatz.Research.StoppingAtlas.Batch0180
