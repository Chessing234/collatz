import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0446

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3763. -/
theorem bounds_12_3763 : exactInterval 12 3763 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3763 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3763) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3763 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3763 : oddCount 3763 12 = 5 ∧ acceleratedOrbit 12 3763 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3763 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3763) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3763.1, data_12_3763.2]

/-- Complete interval computation for depth 12, residue 3764. -/
theorem bounds_12_3764 : exactInterval 12 3764 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3764 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3764) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3764 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3764 : oddCount 3764 12 = 6 ∧ acceleratedOrbit 12 3764 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3764 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3764) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3764.1, data_12_3764.2]

/-- Complete interval computation for depth 12, residue 3765. -/
theorem bounds_12_3765 : exactInterval 12 3765 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3765 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3765) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3765 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3765 : oddCount 3765 12 = 6 ∧ acceleratedOrbit 12 3765 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3765 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3765) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3765.1, data_12_3765.2]

/-- Complete interval computation for depth 12, residue 3766. -/
theorem bounds_12_3766 : exactInterval 12 3766 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3766 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3766) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3766 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3766 : oddCount 3766 12 = 8 ∧ acceleratedOrbit 12 3766 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3766 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3766) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3766.1, data_12_3766.2]

/-- Complete interval computation for depth 12, residue 3767. -/
theorem bounds_12_3767 : exactInterval 12 3767 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3767 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3767) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3767 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3767 : oddCount 3767 12 = 8 ∧ acceleratedOrbit 12 3767 = 6038 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3767 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3767) = 3 ^ 8 * m + 6038 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3767.1, data_12_3767.2]

/-- Complete interval computation for depth 12, residue 3768. -/
theorem bounds_12_3768 : exactInterval 12 3768 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3768 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3768) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3768 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3768 : oddCount 3768 12 = 6 ∧ acceleratedOrbit 12 3768 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3768 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3768) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3768.1, data_12_3768.2]

/-- Complete interval computation for depth 12, residue 3769. -/
theorem bounds_12_3769 : exactInterval 12 3769 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3769 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3769) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3769 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3769 : oddCount 3769 12 = 7 ∧ acceleratedOrbit 12 3769 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3769 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3769) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3769.1, data_12_3769.2]

/-- Complete interval computation for depth 12, residue 3770. -/
theorem bounds_12_3770 : exactInterval 12 3770 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3770 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3770) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3770 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3770 : oddCount 3770 12 = 6 ∧ acceleratedOrbit 12 3770 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3770 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3770) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3770.1, data_12_3770.2]

/-- Complete interval computation for depth 12, residue 3771. -/
theorem bounds_12_3771 : exactInterval 12 3771 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3771 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3771) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3771 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3771 : oddCount 3771 12 = 7 ∧ acceleratedOrbit 12 3771 = 2015 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3771 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3771) = 3 ^ 7 * m + 2015 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3771.1, data_12_3771.2]

/-- Complete interval computation for depth 12, residue 3772. -/
theorem bounds_12_3772 : exactInterval 12 3772 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3772 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3772) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3772 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3772 : oddCount 3772 12 = 5 ∧ acceleratedOrbit 12 3772 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3772 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3772) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3772.1, data_12_3772.2]

/-- Complete interval computation for depth 12, residue 3773. -/
theorem bounds_12_3773 : exactInterval 12 3773 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3773 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3773) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3773 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3773 : oddCount 3773 12 = 5 ∧ acceleratedOrbit 12 3773 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3773 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3773) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3773.1, data_12_3773.2]

/-- Complete interval computation for depth 12, residue 3774. -/
theorem bounds_12_3774 : exactInterval 12 3774 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3774 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3774) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3774 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3774 : oddCount 3774 12 = 5 ∧ acceleratedOrbit 12 3774 = 224 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3774 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3774) = 3 ^ 5 * m + 224 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3774.1, data_12_3774.2]

/-- Complete interval computation for depth 12, residue 3775. -/
theorem bounds_12_3775 : exactInterval 12 3775 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3775 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3775) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3775 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3775 : oddCount 3775 12 = 9 ∧ acceleratedOrbit 12 3775 = 18146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3775 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3775) = 3 ^ 9 * m + 18146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3775.1, data_12_3775.2]

/-- Complete interval computation for depth 12, residue 3776. -/
theorem bounds_12_3776 : exactInterval 12 3776 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3776 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3776) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3776 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3776 : oddCount 3776 12 = 4 ∧ acceleratedOrbit 12 3776 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3776 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3776) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3776.1, data_12_3776.2]

/-- Complete interval computation for depth 12, residue 3777. -/
theorem bounds_12_3777 : exactInterval 12 3777 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3777 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3777) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3777 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3777 : oddCount 3777 12 = 6 ∧ acceleratedOrbit 12 3777 = 674 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3777 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3777) = 3 ^ 6 * m + 674 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3777.1, data_12_3777.2]

end Collatz.Research.StoppingAtlas.Batch0446
