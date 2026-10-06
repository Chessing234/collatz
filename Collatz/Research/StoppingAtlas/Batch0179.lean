import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0179

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1710. -/
theorem bounds_11_1710 : exactInterval 11 1710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1710 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1710) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1710 : oddCount 1710 11 = 6 ∧ acceleratedOrbit 11 1710 = 611 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1710 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1710) = 3 ^ 6 * m + 611 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1710.1, data_11_1710.2]

/-- Complete interval computation for depth 11, residue 1711. -/
theorem bounds_11_1711 : exactInterval 11 1711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1711 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1711) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1711 : oddCount 1711 11 = 7 ∧ acceleratedOrbit 11 1711 = 1829 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1711 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1711) = 3 ^ 7 * m + 1829 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1711.1, data_11_1711.2]

/-- Complete interval computation for depth 11, residue 1712. -/
theorem bounds_11_1712 : exactInterval 11 1712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1712 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1712) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1712 : oddCount 1712 11 = 5 ∧ acceleratedOrbit 11 1712 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1712 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1712) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1712.1, data_11_1712.2]

/-- Complete interval computation for depth 11, residue 1713. -/
theorem bounds_11_1713 : exactInterval 11 1713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1713 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1713) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1713 : oddCount 1713 11 = 4 ∧ acceleratedOrbit 11 1713 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1713 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1713) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1713.1, data_11_1713.2]

/-- Complete interval computation for depth 11, residue 1714. -/
theorem bounds_11_1714 : exactInterval 11 1714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1714 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1714) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1714 : oddCount 1714 11 = 4 ∧ acceleratedOrbit 11 1714 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1714 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1714) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1714.1, data_11_1714.2]

/-- Complete interval computation for depth 11, residue 1715. -/
theorem bounds_11_1715 : exactInterval 11 1715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1715 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1715) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1715 : oddCount 1715 11 = 4 ∧ acceleratedOrbit 11 1715 = 68 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1715 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1715) = 3 ^ 4 * m + 68 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1715.1, data_11_1715.2]

/-- Complete interval computation for depth 11, residue 1716. -/
theorem bounds_11_1716 : exactInterval 11 1716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1716 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1716) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1716 : oddCount 1716 11 = 5 ∧ acceleratedOrbit 11 1716 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1716 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1716) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1716.1, data_11_1716.2]

/-- Complete interval computation for depth 11, residue 1717. -/
theorem bounds_11_1717 : exactInterval 11 1717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1717 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1717) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1717 : oddCount 1717 11 = 5 ∧ acceleratedOrbit 11 1717 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1717 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1717) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1717.1, data_11_1717.2]

/-- Complete interval computation for depth 11, residue 1718. -/
theorem bounds_11_1718 : exactInterval 11 1718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1718 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1718) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1718 : oddCount 1718 11 = 7 ∧ acceleratedOrbit 11 1718 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1718 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1718) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1718.1, data_11_1718.2]

/-- Complete interval computation for depth 11, residue 1719. -/
theorem bounds_11_1719 : exactInterval 11 1719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1719 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1719) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1719 : oddCount 1719 11 = 7 ∧ acceleratedOrbit 11 1719 = 1838 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1719 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1719) = 3 ^ 7 * m + 1838 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1719.1, data_11_1719.2]

/-- Complete interval computation for depth 11, residue 1720. -/
theorem bounds_11_1720 : exactInterval 11 1720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1720 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1720) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1720 : oddCount 1720 11 = 5 ∧ acceleratedOrbit 11 1720 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1720 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1720) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1720.1, data_11_1720.2]

/-- Complete interval computation for depth 11, residue 1721. -/
theorem bounds_11_1721 : exactInterval 11 1721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1721 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1721) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1721 : oddCount 1721 11 = 6 ∧ acceleratedOrbit 11 1721 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1721 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1721) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1721.1, data_11_1721.2]

/-- Complete interval computation for depth 11, residue 1722. -/
theorem bounds_11_1722 : exactInterval 11 1722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1722 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1722) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1722 : oddCount 1722 11 = 5 ∧ acceleratedOrbit 11 1722 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1722 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1722) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1722.1, data_11_1722.2]

/-- Complete interval computation for depth 11, residue 1723. -/
theorem bounds_11_1723 : exactInterval 11 1723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1723 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1723) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1723 : oddCount 1723 11 = 6 ∧ acceleratedOrbit 11 1723 = 614 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1723 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1723) = 3 ^ 6 * m + 614 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1723.1, data_11_1723.2]

/-- Complete interval computation for depth 11, residue 1724. -/
theorem bounds_11_1724 : exactInterval 11 1724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1724 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1724) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1724 : oddCount 1724 11 = 5 ∧ acceleratedOrbit 11 1724 = 205 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1724 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1724) = 3 ^ 5 * m + 205 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1724.1, data_11_1724.2]

end Collatz.Research.StoppingAtlas.Batch0179
