import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0909

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 29753. -/
theorem bounds_15_29753 : exactInterval 15 29753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29753 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29753) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29753 : oddCount 29753 15 = 6 ∧ acceleratedOrbit 15 29753 = 662 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29753 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29753) = 3 ^ 6 * m + 662 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29753.1, data_15_29753.2]

/-- Complete interval computation for depth 15, residue 29754. -/
theorem bounds_15_29754 : exactInterval 15 29754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29754 : oddCount 29754 15 = 7 ∧ acceleratedOrbit 15 29754 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29754) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29754.1, data_15_29754.2]

/-- Complete interval computation for depth 15, residue 29755. -/
theorem bounds_15_29755 : exactInterval 15 29755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29755 : oddCount 29755 15 = 9 ∧ acceleratedOrbit 15 29755 = 17876 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29755) = 3 ^ 9 * m + 17876 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29755.1, data_15_29755.2]

/-- Complete interval computation for depth 15, residue 29756. -/
theorem bounds_15_29756 : exactInterval 15 29756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29756 : oddCount 29756 15 = 7 ∧ acceleratedOrbit 15 29756 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29756) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29756.1, data_15_29756.2]

/-- Complete interval computation for depth 15, residue 29757. -/
theorem bounds_15_29757 : exactInterval 15 29757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29757 : oddCount 29757 15 = 7 ∧ acceleratedOrbit 15 29757 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29757) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29757.1, data_15_29757.2]

/-- Complete interval computation for depth 15, residue 29758. -/
theorem bounds_15_29758 : exactInterval 15 29758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29758 : oddCount 29758 15 = 8 ∧ acceleratedOrbit 15 29758 = 5959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29758) = 3 ^ 8 * m + 5959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29758.1, data_15_29758.2]

/-- Complete interval computation for depth 15, residue 29759. -/
theorem bounds_15_29759 : exactInterval 15 29759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29759) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29759 : oddCount 29759 15 = 8 ∧ acceleratedOrbit 15 29759 = 5959 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29759) = 3 ^ 8 * m + 5959 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29759.1, data_15_29759.2]

/-- Complete interval computation for depth 15, residue 29760. -/
theorem bounds_15_29760 : exactInterval 15 29760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29760 : oddCount 29760 15 = 4 ∧ acceleratedOrbit 15 29760 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29760) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29760.1, data_15_29760.2]

/-- Complete interval computation for depth 15, residue 29761. -/
theorem bounds_15_29761 : exactInterval 15 29761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29761 : oddCount 29761 15 = 7 ∧ acceleratedOrbit 15 29761 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29761) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29761.1, data_15_29761.2]

/-- Complete interval computation for depth 15, residue 29762. -/
theorem bounds_15_29762 : exactInterval 15 29762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29762 : oddCount 29762 15 = 7 ∧ acceleratedOrbit 15 29762 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29762) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29762.1, data_15_29762.2]

/-- Complete interval computation for depth 15, residue 29763. -/
theorem bounds_15_29763 : exactInterval 15 29763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29763 : oddCount 29763 15 = 7 ∧ acceleratedOrbit 15 29763 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29763) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29763.1, data_15_29763.2]

/-- Complete interval computation for depth 15, residue 29764. -/
theorem bounds_15_29764 : exactInterval 15 29764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29764 : oddCount 29764 15 = 5 ∧ acceleratedOrbit 15 29764 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29764) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29764.1, data_15_29764.2]

/-- Complete interval computation for depth 15, residue 29765. -/
theorem bounds_15_29765 : exactInterval 15 29765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29765 : oddCount 29765 15 = 5 ∧ acceleratedOrbit 15 29765 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29765) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29765.1, data_15_29765.2]

/-- Complete interval computation for depth 15, residue 29766. -/
theorem bounds_15_29766 : exactInterval 15 29766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29766 : oddCount 29766 15 = 5 ∧ acceleratedOrbit 15 29766 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29766) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29766.1, data_15_29766.2]

/-- Complete interval computation for depth 15, residue 29767. -/
theorem bounds_15_29767 : exactInterval 15 29767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29767 : oddCount 29767 15 = 9 ∧ acceleratedOrbit 15 29767 = 17882 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29767) = 3 ^ 9 * m + 17882 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29767.1, data_15_29767.2]

/-- Complete interval computation for depth 15, residue 29768. -/
theorem bounds_15_29768 : exactInterval 15 29768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29768 : oddCount 29768 15 = 9 ∧ acceleratedOrbit 15 29768 = 17891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29768) = 3 ^ 9 * m + 17891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29768.1, data_15_29768.2]

/-- Complete interval computation for depth 15, residue 29769. -/
theorem bounds_15_29769 : exactInterval 15 29769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29769 : oddCount 29769 15 = 7 ∧ acceleratedOrbit 15 29769 = 1987 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29769) = 3 ^ 7 * m + 1987 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29769.1, data_15_29769.2]

/-- Complete interval computation for depth 15, residue 29770. -/
theorem bounds_15_29770 : exactInterval 15 29770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29770 : oddCount 29770 15 = 9 ∧ acceleratedOrbit 15 29770 = 17891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29770) = 3 ^ 9 * m + 17891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29770.1, data_15_29770.2]

/-- Complete interval computation for depth 15, residue 29771. -/
theorem bounds_15_29771 : exactInterval 15 29771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29771 : oddCount 29771 15 = 5 ∧ acceleratedOrbit 15 29771 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29771) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29771.1, data_15_29771.2]

/-- Complete interval computation for depth 15, residue 29772. -/
theorem bounds_15_29772 : exactInterval 15 29772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29772 : oddCount 29772 15 = 9 ∧ acceleratedOrbit 15 29772 = 17891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29772) = 3 ^ 9 * m + 17891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29772.1, data_15_29772.2]

/-- Complete interval computation for depth 15, residue 29773. -/
theorem bounds_15_29773 : exactInterval 15 29773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29773 : oddCount 29773 15 = 9 ∧ acceleratedOrbit 15 29773 = 17891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29773) = 3 ^ 9 * m + 17891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29773.1, data_15_29773.2]

/-- Complete interval computation for depth 15, residue 29774. -/
theorem bounds_15_29774 : exactInterval 15 29774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29774 : oddCount 29774 15 = 7 ∧ acceleratedOrbit 15 29774 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29774) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29774.1, data_15_29774.2]

/-- Complete interval computation for depth 15, residue 29775. -/
theorem bounds_15_29775 : exactInterval 15 29775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29775 : oddCount 29775 15 = 7 ∧ acceleratedOrbit 15 29775 = 1988 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29775) = 3 ^ 7 * m + 1988 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29775.1, data_15_29775.2]

/-- Complete interval computation for depth 15, residue 29776. -/
theorem bounds_15_29776 : exactInterval 15 29776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29776 : oddCount 29776 15 = 4 ∧ acceleratedOrbit 15 29776 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29776) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29776.1, data_15_29776.2]

/-- Complete interval computation for depth 15, residue 29777. -/
theorem bounds_15_29777 : exactInterval 15 29777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29777 : oddCount 29777 15 = 9 ∧ acceleratedOrbit 15 29777 = 17891 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29777) = 3 ^ 9 * m + 17891 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29777.1, data_15_29777.2]

/-- Complete interval computation for depth 15, residue 29778. -/
theorem bounds_15_29778 : exactInterval 15 29778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29778 : oddCount 29778 15 = 8 ∧ acceleratedOrbit 15 29778 = 5963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29778) = 3 ^ 8 * m + 5963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29778.1, data_15_29778.2]

/-- Complete interval computation for depth 15, residue 29779. -/
theorem bounds_15_29779 : exactInterval 15 29779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29779 : oddCount 29779 15 = 8 ∧ acceleratedOrbit 15 29779 = 5963 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29779) = 3 ^ 8 * m + 5963 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29779.1, data_15_29779.2]

/-- Complete interval computation for depth 15, residue 29780. -/
theorem bounds_15_29780 : exactInterval 15 29780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29780 : oddCount 29780 15 = 4 ∧ acceleratedOrbit 15 29780 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29780) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29780.1, data_15_29780.2]

/-- Complete interval computation for depth 15, residue 29781. -/
theorem bounds_15_29781 : exactInterval 15 29781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29781 : oddCount 29781 15 = 4 ∧ acceleratedOrbit 15 29781 = 74 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29781) = 3 ^ 4 * m + 74 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29781.1, data_15_29781.2]

/-- Complete interval computation for depth 15, residue 29782. -/
theorem bounds_15_29782 : exactInterval 15 29782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29782 : oddCount 29782 15 = 5 ∧ acceleratedOrbit 15 29782 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29782) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29782.1, data_15_29782.2]

/-- Complete interval computation for depth 15, residue 29783. -/
theorem bounds_15_29783 : exactInterval 15 29783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29783 : oddCount 29783 15 = 5 ∧ acceleratedOrbit 15 29783 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29783) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29783.1, data_15_29783.2]

/-- Complete interval computation for depth 15, residue 29784. -/
theorem bounds_15_29784 : exactInterval 15 29784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29784 : oddCount 29784 15 = 5 ∧ acceleratedOrbit 15 29784 = 221 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29784) = 3 ^ 5 * m + 221 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29784.1, data_15_29784.2]

/-- Complete interval computation for depth 15, residue 29785. -/
theorem bounds_15_29785 : exactInterval 15 29785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_29785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 29785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_29785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_29785 : oddCount 29785 15 = 8 ∧ acceleratedOrbit 15 29785 = 5966 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_29785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 29785) = 3 ^ 8 * m + 5966 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_29785.1, data_15_29785.2]

end Collatz.Research.PassageAtlas.Batch0909
