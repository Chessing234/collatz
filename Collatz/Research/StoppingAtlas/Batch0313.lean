import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0313

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1720. -/
theorem bounds_12_1720 : exactInterval 12 1720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1720 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1720) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1720 : oddCount 1720 12 = 5 ∧ acceleratedOrbit 12 1720 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1720 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1720) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1720.1, data_12_1720.2]

/-- Complete interval computation for depth 12, residue 1721. -/
theorem bounds_12_1721 : exactInterval 12 1721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1721 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1721) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1721 : oddCount 1721 12 = 6 ∧ acceleratedOrbit 12 1721 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1721 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1721) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1721.1, data_12_1721.2]

/-- Complete interval computation for depth 12, residue 1722. -/
theorem bounds_12_1722 : exactInterval 12 1722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1722 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1722) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1722 : oddCount 1722 12 = 5 ∧ acceleratedOrbit 12 1722 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1722 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1722) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1722.1, data_12_1722.2]

/-- Complete interval computation for depth 12, residue 1723. -/
theorem bounds_12_1723 : exactInterval 12 1723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1723 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1723) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1723 : oddCount 1723 12 = 6 ∧ acceleratedOrbit 12 1723 = 307 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1723 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1723) = 3 ^ 6 * m + 307 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1723.1, data_12_1723.2]

/-- Complete interval computation for depth 12, residue 1724. -/
theorem bounds_12_1724 : exactInterval 12 1724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1724 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1724) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1724 : oddCount 1724 12 = 6 ∧ acceleratedOrbit 12 1724 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1724 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1724) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1724.1, data_12_1724.2]

/-- Complete interval computation for depth 12, residue 1725. -/
theorem bounds_12_1725 : exactInterval 12 1725 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1725 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1725) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1725 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1725 : oddCount 1725 12 = 6 ∧ acceleratedOrbit 12 1725 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1725 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1725) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1725.1, data_12_1725.2]

/-- Complete interval computation for depth 12, residue 1726. -/
theorem bounds_12_1726 : exactInterval 12 1726 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1726 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1726) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1726 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1726 : oddCount 1726 12 = 6 ∧ acceleratedOrbit 12 1726 = 308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1726 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1726) = 3 ^ 6 * m + 308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1726.1, data_12_1726.2]

/-- Complete interval computation for depth 12, residue 1727. -/
theorem bounds_12_1727 : exactInterval 12 1727 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1727 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1727) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1727 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1727 : oddCount 1727 12 = 8 ∧ acceleratedOrbit 12 1727 = 2768 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1727 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1727) = 3 ^ 8 * m + 2768 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1727.1, data_12_1727.2]

/-- Complete interval computation for depth 12, residue 1728. -/
theorem bounds_12_1728 : exactInterval 12 1728 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1728 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1728) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1728 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1728 : oddCount 1728 12 = 5 ∧ acceleratedOrbit 12 1728 = 107 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1728 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1728) = 3 ^ 5 * m + 107 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1728.1, data_12_1728.2]

/-- Complete interval computation for depth 12, residue 1729. -/
theorem bounds_12_1729 : exactInterval 12 1729 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1729 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1729) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1729 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1729 : oddCount 1729 12 = 5 ∧ acceleratedOrbit 12 1729 = 103 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1729 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1729) = 3 ^ 5 * m + 103 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1729.1, data_12_1729.2]

/-- Complete interval computation for depth 12, residue 1730. -/
theorem bounds_12_1730 : exactInterval 12 1730 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1730 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1730) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1730 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1730 : oddCount 1730 12 = 8 ∧ acceleratedOrbit 12 1730 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1730 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1730) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1730.1, data_12_1730.2]

/-- Complete interval computation for depth 12, residue 1731. -/
theorem bounds_12_1731 : exactInterval 12 1731 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1731 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1731) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1731 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1731 : oddCount 1731 12 = 8 ∧ acceleratedOrbit 12 1731 = 2780 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1731 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1731) = 3 ^ 8 * m + 2780 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1731.1, data_12_1731.2]

/-- Complete interval computation for depth 12, residue 1732. -/
theorem bounds_12_1732 : exactInterval 12 1732 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1732 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1732) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1732 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1732 : oddCount 1732 12 = 4 ∧ acceleratedOrbit 12 1732 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1732 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1732) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1732.1, data_12_1732.2]

/-- Complete interval computation for depth 12, residue 1733. -/
theorem bounds_12_1733 : exactInterval 12 1733 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1733 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1733) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1733 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1733 : oddCount 1733 12 = 4 ∧ acceleratedOrbit 12 1733 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1733 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1733) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1733.1, data_12_1733.2]

/-- Complete interval computation for depth 12, residue 1734. -/
theorem bounds_12_1734 : exactInterval 12 1734 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1734 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1734) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1734 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1734 : oddCount 1734 12 = 4 ∧ acceleratedOrbit 12 1734 = 35 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1734 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1734) = 3 ^ 4 * m + 35 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1734.1, data_12_1734.2]

end Collatz.Research.StoppingAtlas.Batch0313
