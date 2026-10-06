import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0848

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27754. -/
theorem bounds_15_27754 : exactInterval 15 27754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27754 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27754) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27754 : oddCount 27754 15 = 3 ∧ acceleratedOrbit 15 27754 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27754 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27754) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27754.1, data_15_27754.2]

/-- Complete interval computation for depth 15, residue 27755. -/
theorem bounds_15_27755 : exactInterval 15 27755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27755 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27755) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27755 : oddCount 27755 15 = 10 ∧ acceleratedOrbit 15 27755 = 50021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27755 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27755) = 3 ^ 10 * m + 50021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27755.1, data_15_27755.2]

/-- Complete interval computation for depth 15, residue 27756. -/
theorem bounds_15_27756 : exactInterval 15 27756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27756 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27756) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27756 : oddCount 27756 15 = 11 ∧ acceleratedOrbit 15 27756 = 150083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27756 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27756) = 3 ^ 11 * m + 150083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27756.1, data_15_27756.2]

/-- Complete interval computation for depth 15, residue 27757. -/
theorem bounds_15_27757 : exactInterval 15 27757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27757 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27757) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27757 : oddCount 27757 15 = 11 ∧ acceleratedOrbit 15 27757 = 150083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27757 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27757) = 3 ^ 11 * m + 150083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27757.1, data_15_27757.2]

/-- Complete interval computation for depth 15, residue 27758. -/
theorem bounds_15_27758 : exactInterval 15 27758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27758 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27758) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27758 : oddCount 27758 15 = 11 ∧ acceleratedOrbit 15 27758 = 150083 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27758 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27758) = 3 ^ 11 * m + 150083 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27758.1, data_15_27758.2]

/-- Complete interval computation for depth 15, residue 27759. -/
theorem bounds_15_27759 : exactInterval 15 27759 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27759 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27759) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27759 : oddCount 27759 15 = 9 ∧ acceleratedOrbit 15 27759 = 16675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27759 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27759) = 3 ^ 9 * m + 16675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27759.1, data_15_27759.2]

/-- Complete interval computation for depth 15, residue 27760. -/
theorem bounds_15_27760 : exactInterval 15 27760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27760 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27760) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27760 : oddCount 27760 15 = 5 ∧ acceleratedOrbit 15 27760 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27760 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27760) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27760.1, data_15_27760.2]

/-- Complete interval computation for depth 15, residue 27761. -/
theorem bounds_15_27761 : exactInterval 15 27761 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27761 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27761) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27761 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27761 : oddCount 27761 15 = 3 ∧ acceleratedOrbit 15 27761 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27761 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27761) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27761.1, data_15_27761.2]

/-- Complete interval computation for depth 15, residue 27762. -/
theorem bounds_15_27762 : exactInterval 15 27762 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27762 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27762) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27762 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27762 : oddCount 27762 15 = 8 ∧ acceleratedOrbit 15 27762 = 5561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27762 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27762) = 3 ^ 8 * m + 5561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27762.1, data_15_27762.2]

/-- Complete interval computation for depth 15, residue 27763. -/
theorem bounds_15_27763 : exactInterval 15 27763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27763 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27763) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27763 : oddCount 27763 15 = 8 ∧ acceleratedOrbit 15 27763 = 5561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27763 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27763) = 3 ^ 8 * m + 5561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27763.1, data_15_27763.2]

/-- Complete interval computation for depth 15, residue 27764. -/
theorem bounds_15_27764 : exactInterval 15 27764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27764 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27764) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27764 : oddCount 27764 15 = 5 ∧ acceleratedOrbit 15 27764 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27764 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27764) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27764.1, data_15_27764.2]

/-- Complete interval computation for depth 15, residue 27765. -/
theorem bounds_15_27765 : exactInterval 15 27765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27765 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27765) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27765 : oddCount 27765 15 = 5 ∧ acceleratedOrbit 15 27765 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27765 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27765) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27765.1, data_15_27765.2]

/-- Complete interval computation for depth 15, residue 27766. -/
theorem bounds_15_27766 : exactInterval 15 27766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27766 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27766) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27766 : oddCount 27766 15 = 9 ∧ acceleratedOrbit 15 27766 = 16685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27766 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27766) = 3 ^ 9 * m + 16685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27766.1, data_15_27766.2]

/-- Complete interval computation for depth 15, residue 27767. -/
theorem bounds_15_27767 : exactInterval 15 27767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27767 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27767) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27767 : oddCount 27767 15 = 9 ∧ acceleratedOrbit 15 27767 = 16685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27767 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27767) = 3 ^ 9 * m + 16685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27767.1, data_15_27767.2]

/-- Complete interval computation for depth 15, residue 27768. -/
theorem bounds_15_27768 : exactInterval 15 27768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27768 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27768) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27768 : oddCount 27768 15 = 5 ∧ acceleratedOrbit 15 27768 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27768 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27768) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27768.1, data_15_27768.2]

/-- Complete interval computation for depth 15, residue 27769. -/
theorem bounds_15_27769 : exactInterval 15 27769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27769 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27769) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27769 : oddCount 27769 15 = 8 ∧ acceleratedOrbit 15 27769 = 5561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27769 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27769) = 3 ^ 8 * m + 5561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27769.1, data_15_27769.2]

/-- Complete interval computation for depth 15, residue 27770. -/
theorem bounds_15_27770 : exactInterval 15 27770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27770 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27770) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27770 : oddCount 27770 15 = 5 ∧ acceleratedOrbit 15 27770 = 206 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27770 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27770) = 3 ^ 5 * m + 206 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27770.1, data_15_27770.2]

/-- Complete interval computation for depth 15, residue 27771. -/
theorem bounds_15_27771 : exactInterval 15 27771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27771 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27771) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27771 : oddCount 27771 15 = 9 ∧ acceleratedOrbit 15 27771 = 16685 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27771 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27771) = 3 ^ 9 * m + 16685 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27771.1, data_15_27771.2]

/-- Complete interval computation for depth 15, residue 27772. -/
theorem bounds_15_27772 : exactInterval 15 27772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27772 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27772) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27772 : oddCount 27772 15 = 10 ∧ acceleratedOrbit 15 27772 = 50057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27772 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27772) = 3 ^ 10 * m + 50057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27772.1, data_15_27772.2]

/-- Complete interval computation for depth 15, residue 27773. -/
theorem bounds_15_27773 : exactInterval 15 27773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27773 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27773) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27773 : oddCount 27773 15 = 10 ∧ acceleratedOrbit 15 27773 = 50057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27773 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27773) = 3 ^ 10 * m + 50057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27773.1, data_15_27773.2]

/-- Complete interval computation for depth 15, residue 27774. -/
theorem bounds_15_27774 : exactInterval 15 27774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27774 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27774) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27774 : oddCount 27774 15 = 10 ∧ acceleratedOrbit 15 27774 = 50057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27774 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27774) = 3 ^ 10 * m + 50057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27774.1, data_15_27774.2]

/-- Complete interval computation for depth 15, residue 27775. -/
theorem bounds_15_27775 : exactInterval 15 27775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27775 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27775) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27775 : oddCount 27775 15 = 12 ∧ acceleratedOrbit 15 27775 = 450481 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27775 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27775) = 3 ^ 12 * m + 450481 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27775.1, data_15_27775.2]

/-- Complete interval computation for depth 15, residue 27776. -/
theorem bounds_15_27776 : exactInterval 15 27776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27776 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27776) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27776 : oddCount 27776 15 = 3 ∧ acceleratedOrbit 15 27776 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27776 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27776) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27776.1, data_15_27776.2]

/-- Complete interval computation for depth 15, residue 27777. -/
theorem bounds_15_27777 : exactInterval 15 27777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27777 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27777) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27777 : oddCount 27777 15 = 9 ∧ acceleratedOrbit 15 27777 = 16688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27777 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27777) = 3 ^ 9 * m + 16688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27777.1, data_15_27777.2]

/-- Complete interval computation for depth 15, residue 27778. -/
theorem bounds_15_27778 : exactInterval 15 27778 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27778 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27778) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27778 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27778 : oddCount 27778 15 = 7 ∧ acceleratedOrbit 15 27778 = 1856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27778 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27778) = 3 ^ 7 * m + 1856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27778.1, data_15_27778.2]

/-- Complete interval computation for depth 15, residue 27779. -/
theorem bounds_15_27779 : exactInterval 15 27779 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27779 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27779) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27779 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27779 : oddCount 27779 15 = 7 ∧ acceleratedOrbit 15 27779 = 1856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27779 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27779) = 3 ^ 7 * m + 1856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27779.1, data_15_27779.2]

/-- Complete interval computation for depth 15, residue 27780. -/
theorem bounds_15_27780 : exactInterval 15 27780 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27780 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27780) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27780 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27780 : oddCount 27780 15 = 7 ∧ acceleratedOrbit 15 27780 = 1856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27780 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27780) = 3 ^ 7 * m + 1856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27780.1, data_15_27780.2]

/-- Complete interval computation for depth 15, residue 27781. -/
theorem bounds_15_27781 : exactInterval 15 27781 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27781 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27781) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27781 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27781 : oddCount 27781 15 = 7 ∧ acceleratedOrbit 15 27781 = 1856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27781 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27781) = 3 ^ 7 * m + 1856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27781.1, data_15_27781.2]

/-- Complete interval computation for depth 15, residue 27782. -/
theorem bounds_15_27782 : exactInterval 15 27782 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27782 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27782) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27782 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27782 : oddCount 27782 15 = 7 ∧ acceleratedOrbit 15 27782 = 1856 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27782 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27782) = 3 ^ 7 * m + 1856 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27782.1, data_15_27782.2]

/-- Complete interval computation for depth 15, residue 27783. -/
theorem bounds_15_27783 : exactInterval 15 27783 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27783 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27783) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27783 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27783 : oddCount 27783 15 = 8 ∧ acceleratedOrbit 15 27783 = 5564 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27783 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27783) = 3 ^ 8 * m + 5564 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27783.1, data_15_27783.2]

/-- Complete interval computation for depth 15, residue 27784. -/
theorem bounds_15_27784 : exactInterval 15 27784 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27784 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27784) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27784 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27784 : oddCount 27784 15 = 6 ∧ acceleratedOrbit 15 27784 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27784 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27784) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27784.1, data_15_27784.2]

/-- Complete interval computation for depth 15, residue 27785. -/
theorem bounds_15_27785 : exactInterval 15 27785 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27785 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27785) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27785 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27785 : oddCount 27785 15 = 9 ∧ acceleratedOrbit 15 27785 = 16691 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27785 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27785) = 3 ^ 9 * m + 16691 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27785.1, data_15_27785.2]

/-- Complete interval computation for depth 15, residue 27786. -/
theorem bounds_15_27786 : exactInterval 15 27786 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27786 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27786) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27786 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27786 : oddCount 27786 15 = 6 ∧ acceleratedOrbit 15 27786 = 620 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27786 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27786) = 3 ^ 6 * m + 620 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27786.1, data_15_27786.2]

end Collatz.Research.PassageAtlas.Batch0848
