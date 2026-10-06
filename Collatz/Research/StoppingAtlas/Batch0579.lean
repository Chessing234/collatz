import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0579

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1710. -/
theorem bounds_13_1710 : exactInterval 13 1710 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1710 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1710) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1710 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1710 : oddCount 1710 13 = 8 ∧ acceleratedOrbit 13 1710 = 1376 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1710 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1710) = 3 ^ 8 * m + 1376 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1710.1, data_13_1710.2]

/-- Complete interval computation for depth 13, residue 1711. -/
theorem bounds_13_1711 : exactInterval 13 1711 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1711 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1711) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1711 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1711 : oddCount 1711 13 = 8 ∧ acceleratedOrbit 13 1711 = 1372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1711 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1711) = 3 ^ 8 * m + 1372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1711.1, data_13_1711.2]

/-- Complete interval computation for depth 13, residue 1712. -/
theorem bounds_13_1712 : exactInterval 13 1712 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1712 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1712) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1712 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1712 : oddCount 1712 13 = 6 ∧ acceleratedOrbit 13 1712 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1712 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1712) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1712.1, data_13_1712.2]

/-- Complete interval computation for depth 13, residue 1713. -/
theorem bounds_13_1713 : exactInterval 13 1713 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1713 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1713) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1713 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1713 : oddCount 1713 13 = 4 ∧ acceleratedOrbit 13 1713 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1713 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1713) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1713.1, data_13_1713.2]

/-- Complete interval computation for depth 13, residue 1714. -/
theorem bounds_13_1714 : exactInterval 13 1714 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1714 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1714) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1714 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1714 : oddCount 1714 13 = 4 ∧ acceleratedOrbit 13 1714 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1714 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1714) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1714.1, data_13_1714.2]

/-- Complete interval computation for depth 13, residue 1715. -/
theorem bounds_13_1715 : exactInterval 13 1715 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1715 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1715) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1715 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1715 : oddCount 1715 13 = 4 ∧ acceleratedOrbit 13 1715 = 17 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1715 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1715) = 3 ^ 4 * m + 17 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1715.1, data_13_1715.2]

/-- Complete interval computation for depth 13, residue 1716. -/
theorem bounds_13_1716 : exactInterval 13 1716 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1716 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1716) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1716 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1716 : oddCount 1716 13 = 6 ∧ acceleratedOrbit 13 1716 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1716 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1716) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1716.1, data_13_1716.2]

/-- Complete interval computation for depth 13, residue 1717. -/
theorem bounds_13_1717 : exactInterval 13 1717 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1717 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1717) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1717 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1717 : oddCount 1717 13 = 6 ∧ acceleratedOrbit 13 1717 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1717 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1717) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1717.1, data_13_1717.2]

/-- Complete interval computation for depth 13, residue 1718. -/
theorem bounds_13_1718 : exactInterval 13 1718 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1718 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1718) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1718 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1718 : oddCount 1718 13 = 8 ∧ acceleratedOrbit 13 1718 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1718 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1718) = 3 ^ 8 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1718.1, data_13_1718.2]

/-- Complete interval computation for depth 13, residue 1719. -/
theorem bounds_13_1719 : exactInterval 13 1719 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1719 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1719) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1719 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1719 : oddCount 1719 13 = 8 ∧ acceleratedOrbit 13 1719 = 1379 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1719 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1719) = 3 ^ 8 * m + 1379 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1719.1, data_13_1719.2]

/-- Complete interval computation for depth 13, residue 1720. -/
theorem bounds_13_1720 : exactInterval 13 1720 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1720 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1720) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1720 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1720 : oddCount 1720 13 = 6 ∧ acceleratedOrbit 13 1720 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1720 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1720) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1720.1, data_13_1720.2]

/-- Complete interval computation for depth 13, residue 1721. -/
theorem bounds_13_1721 : exactInterval 13 1721 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1721 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1721) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1721 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1721 : oddCount 1721 13 = 7 ∧ acceleratedOrbit 13 1721 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1721 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1721) = 3 ^ 7 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1721.1, data_13_1721.2]

/-- Complete interval computation for depth 13, residue 1722. -/
theorem bounds_13_1722 : exactInterval 13 1722 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1722 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1722) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1722 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1722 : oddCount 1722 13 = 6 ∧ acceleratedOrbit 13 1722 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1722 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1722) = 3 ^ 6 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1722.1, data_13_1722.2]

/-- Complete interval computation for depth 13, residue 1723. -/
theorem bounds_13_1723 : exactInterval 13 1723 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1723 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1723) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1723 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1723 : oddCount 1723 13 = 7 ∧ acceleratedOrbit 13 1723 = 461 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1723 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1723) = 3 ^ 7 * m + 461 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1723.1, data_13_1723.2]

/-- Complete interval computation for depth 13, residue 1724. -/
theorem bounds_13_1724 : exactInterval 13 1724 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1724 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1724) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1724 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1724 : oddCount 1724 13 = 6 ∧ acceleratedOrbit 13 1724 = 154 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1724 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1724) = 3 ^ 6 * m + 154 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1724.1, data_13_1724.2]

end Collatz.Research.StoppingAtlas.Batch0579
