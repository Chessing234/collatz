import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0972

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 7746. -/
theorem bounds_13_7746 : exactInterval 13 7746 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7746 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7746) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7746 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7746 : oddCount 7746 13 = 5 ∧ acceleratedOrbit 13 7746 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7746 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7746) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7746.1, data_13_7746.2]

/-- Complete interval computation for depth 13, residue 7747. -/
theorem bounds_13_7747 : exactInterval 13 7747 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7747 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7747) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7747 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7747 : oddCount 7747 13 = 5 ∧ acceleratedOrbit 13 7747 = 230 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7747 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7747) = 3 ^ 5 * m + 230 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7747.1, data_13_7747.2]

/-- Complete interval computation for depth 13, residue 7748. -/
theorem bounds_13_7748 : exactInterval 13 7748 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7748 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7748) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7748 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7748 : oddCount 7748 13 = 6 ∧ acceleratedOrbit 13 7748 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7748 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7748) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7748.1, data_13_7748.2]

/-- Complete interval computation for depth 13, residue 7749. -/
theorem bounds_13_7749 : exactInterval 13 7749 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7749 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7749) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7749 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7749 : oddCount 7749 13 = 6 ∧ acceleratedOrbit 13 7749 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7749 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7749) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7749.1, data_13_7749.2]

/-- Complete interval computation for depth 13, residue 7750. -/
theorem bounds_13_7750 : exactInterval 13 7750 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7750 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7750) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7750 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7750 : oddCount 7750 13 = 6 ∧ acceleratedOrbit 13 7750 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7750 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7750) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7750.1, data_13_7750.2]

/-- Complete interval computation for depth 13, residue 7751. -/
theorem bounds_13_7751 : exactInterval 13 7751 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7751 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7751) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7751 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7751 : oddCount 7751 13 = 9 ∧ acceleratedOrbit 13 7751 = 18629 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7751 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7751) = 3 ^ 9 * m + 18629 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7751.1, data_13_7751.2]

/-- Complete interval computation for depth 13, residue 7752. -/
theorem bounds_13_7752 : exactInterval 13 7752 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7752 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7752) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7752 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7752 : oddCount 7752 13 = 6 ∧ acceleratedOrbit 13 7752 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7752 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7752) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7752.1, data_13_7752.2]

/-- Complete interval computation for depth 13, residue 7753. -/
theorem bounds_13_7753 : exactInterval 13 7753 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7753 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7753) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7753 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7753 : oddCount 7753 13 = 8 ∧ acceleratedOrbit 13 7753 = 6212 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7753 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7753) = 3 ^ 8 * m + 6212 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7753.1, data_13_7753.2]

/-- Complete interval computation for depth 13, residue 7754. -/
theorem bounds_13_7754 : exactInterval 13 7754 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7754 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7754) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7754 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7754 : oddCount 7754 13 = 6 ∧ acceleratedOrbit 13 7754 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7754 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7754) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7754.1, data_13_7754.2]

/-- Complete interval computation for depth 13, residue 7755. -/
theorem bounds_13_7755 : exactInterval 13 7755 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7755 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7755) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7755 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7755 : oddCount 7755 13 = 6 ∧ acceleratedOrbit 13 7755 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7755 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7755) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7755.1, data_13_7755.2]

/-- Complete interval computation for depth 13, residue 7756. -/
theorem bounds_13_7756 : exactInterval 13 7756 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7756 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7756) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7756 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7756 : oddCount 7756 13 = 6 ∧ acceleratedOrbit 13 7756 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7756 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7756) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7756.1, data_13_7756.2]

/-- Complete interval computation for depth 13, residue 7757. -/
theorem bounds_13_7757 : exactInterval 13 7757 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7757 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7757) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7757 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7757 : oddCount 7757 13 = 6 ∧ acceleratedOrbit 13 7757 = 692 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7757 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7757) = 3 ^ 6 * m + 692 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7757.1, data_13_7757.2]

/-- Complete interval computation for depth 13, residue 7758. -/
theorem bounds_13_7758 : exactInterval 13 7758 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7758 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7758) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7758 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7758 : oddCount 7758 13 = 7 ∧ acceleratedOrbit 13 7758 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7758 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7758) = 3 ^ 7 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7758.1, data_13_7758.2]

/-- Complete interval computation for depth 13, residue 7759. -/
theorem bounds_13_7759 : exactInterval 13 7759 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7759 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7759) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7759 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7759 : oddCount 7759 13 = 7 ∧ acceleratedOrbit 13 7759 = 2072 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7759 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7759) = 3 ^ 7 * m + 2072 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7759.1, data_13_7759.2]

/-- Complete interval computation for depth 13, residue 7760. -/
theorem bounds_13_7760 : exactInterval 13 7760 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_7760 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 7760) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_7760 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_7760 : oddCount 7760 13 = 5 ∧ acceleratedOrbit 13 7760 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_7760 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 7760) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_7760.1, data_13_7760.2]

end Collatz.Research.StoppingAtlas.Batch0972
