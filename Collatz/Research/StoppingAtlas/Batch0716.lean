import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0716

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 3814. -/
theorem bounds_13_3814 : exactInterval 13 3814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3814 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3814) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3814 : oddCount 3814 13 = 6 ∧ acceleratedOrbit 13 3814 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3814 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3814) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3814.1, data_13_3814.2]

/-- Complete interval computation for depth 13, residue 3815. -/
theorem bounds_13_3815 : exactInterval 13 3815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3815 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3815) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3815 : oddCount 3815 13 = 9 ∧ acceleratedOrbit 13 3815 = 9170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3815 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3815) = 3 ^ 9 * m + 9170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3815.1, data_13_3815.2]

/-- Complete interval computation for depth 13, residue 3816. -/
theorem bounds_13_3816 : exactInterval 13 3816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3816 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3816) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3816 : oddCount 3816 13 = 4 ∧ acceleratedOrbit 13 3816 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3816 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3816) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3816.1, data_13_3816.2]

/-- Complete interval computation for depth 13, residue 3817. -/
theorem bounds_13_3817 : exactInterval 13 3817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3817 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3817) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3817 : oddCount 3817 13 = 8 ∧ acceleratedOrbit 13 3817 = 3059 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3817 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3817) = 3 ^ 8 * m + 3059 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3817.1, data_13_3817.2]

/-- Complete interval computation for depth 13, residue 3818. -/
theorem bounds_13_3818 : exactInterval 13 3818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3818 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3818) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3818 : oddCount 3818 13 = 4 ∧ acceleratedOrbit 13 3818 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3818 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3818) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3818.1, data_13_3818.2]

/-- Complete interval computation for depth 13, residue 3819. -/
theorem bounds_13_3819 : exactInterval 13 3819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3819 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3819) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3819 : oddCount 3819 13 = 6 ∧ acceleratedOrbit 13 3819 = 340 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3819 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3819) = 3 ^ 6 * m + 340 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3819.1, data_13_3819.2]

/-- Complete interval computation for depth 13, residue 3820. -/
theorem bounds_13_3820 : exactInterval 13 3820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3820 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3820) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3820 : oddCount 3820 13 = 6 ∧ acceleratedOrbit 13 3820 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3820 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3820) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3820.1, data_13_3820.2]

/-- Complete interval computation for depth 13, residue 3821. -/
theorem bounds_13_3821 : exactInterval 13 3821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3821 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3821) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3821 : oddCount 3821 13 = 6 ∧ acceleratedOrbit 13 3821 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3821 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3821) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3821.1, data_13_3821.2]

/-- Complete interval computation for depth 13, residue 3822. -/
theorem bounds_13_3822 : exactInterval 13 3822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3822 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3822) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3822 : oddCount 3822 13 = 6 ∧ acceleratedOrbit 13 3822 = 341 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3822 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3822) = 3 ^ 6 * m + 341 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3822.1, data_13_3822.2]

/-- Complete interval computation for depth 13, residue 3823. -/
theorem bounds_13_3823 : exactInterval 13 3823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3823 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3823) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3823 : oddCount 3823 13 = 10 ∧ acceleratedOrbit 13 3823 = 27566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3823 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3823) = 3 ^ 10 * m + 27566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3823.1, data_13_3823.2]

/-- Complete interval computation for depth 13, residue 3824. -/
theorem bounds_13_3824 : exactInterval 13 3824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3824 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3824) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3824 : oddCount 3824 13 = 8 ∧ acceleratedOrbit 13 3824 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3824 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3824) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3824.1, data_13_3824.2]

/-- Complete interval computation for depth 13, residue 3825. -/
theorem bounds_13_3825 : exactInterval 13 3825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3825 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3825) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3825 : oddCount 3825 13 = 4 ∧ acceleratedOrbit 13 3825 = 38 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3825 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3825) = 3 ^ 4 * m + 38 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3825.1, data_13_3825.2]

/-- Complete interval computation for depth 13, residue 3826. -/
theorem bounds_13_3826 : exactInterval 13 3826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3826 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3826) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3826 : oddCount 3826 13 = 8 ∧ acceleratedOrbit 13 3826 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3826 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3826) = 3 ^ 8 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3826.1, data_13_3826.2]

/-- Complete interval computation for depth 13, residue 3827. -/
theorem bounds_13_3827 : exactInterval 13 3827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3827 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3827) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3827 : oddCount 3827 13 = 8 ∧ acceleratedOrbit 13 3827 = 3068 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3827 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3827) = 3 ^ 8 * m + 3068 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3827.1, data_13_3827.2]

/-- Complete interval computation for depth 13, residue 3828. -/
theorem bounds_13_3828 : exactInterval 13 3828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_3828 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 3828) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_3828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_3828 : oddCount 3828 13 = 8 ∧ acceleratedOrbit 13 3828 = 3077 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_3828 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 3828) = 3 ^ 8 * m + 3077 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_3828.1, data_13_3828.2]

end Collatz.Research.StoppingAtlas.Batch0716
