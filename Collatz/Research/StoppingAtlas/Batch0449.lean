import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0449

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 3809. -/
theorem bounds_12_3809 : exactInterval 12 3809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3809 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3809) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3809 : oddCount 3809 12 = 7 ∧ acceleratedOrbit 12 3809 = 2035 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3809 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3809) = 3 ^ 7 * m + 2035 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3809.1, data_12_3809.2]

/-- Complete interval computation for depth 12, residue 3810. -/
theorem bounds_12_3810 : exactInterval 12 3810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3810 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3810) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3810 : oddCount 3810 12 = 4 ∧ acceleratedOrbit 12 3810 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3810 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3810) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3810.1, data_12_3810.2]

/-- Complete interval computation for depth 12, residue 3811. -/
theorem bounds_12_3811 : exactInterval 12 3811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3811 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3811) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3811 : oddCount 3811 12 = 4 ∧ acceleratedOrbit 12 3811 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3811 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3811) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3811.1, data_12_3811.2]

/-- Complete interval computation for depth 12, residue 3812. -/
theorem bounds_12_3812 : exactInterval 12 3812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3812 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3812) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3812 : oddCount 3812 12 = 5 ∧ acceleratedOrbit 12 3812 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3812 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3812) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3812.1, data_12_3812.2]

/-- Complete interval computation for depth 12, residue 3813. -/
theorem bounds_12_3813 : exactInterval 12 3813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3813 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3813) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3813 : oddCount 3813 12 = 5 ∧ acceleratedOrbit 12 3813 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3813 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3813) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3813.1, data_12_3813.2]

/-- Complete interval computation for depth 12, residue 3814. -/
theorem bounds_12_3814 : exactInterval 12 3814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3814 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3814) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3814 : oddCount 3814 12 = 5 ∧ acceleratedOrbit 12 3814 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3814 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3814) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3814.1, data_12_3814.2]

/-- Complete interval computation for depth 12, residue 3815. -/
theorem bounds_12_3815 : exactInterval 12 3815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3815 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3815) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3815 : oddCount 3815 12 = 8 ∧ acceleratedOrbit 12 3815 = 6113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3815 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3815) = 3 ^ 8 * m + 6113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3815.1, data_12_3815.2]

/-- Complete interval computation for depth 12, residue 3816. -/
theorem bounds_12_3816 : exactInterval 12 3816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3816 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3816) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3816 : oddCount 3816 12 = 4 ∧ acceleratedOrbit 12 3816 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3816 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3816) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3816.1, data_12_3816.2]

/-- Complete interval computation for depth 12, residue 3817. -/
theorem bounds_12_3817 : exactInterval 12 3817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3817 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3817) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3817 : oddCount 3817 12 = 7 ∧ acceleratedOrbit 12 3817 = 2039 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3817 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3817) = 3 ^ 7 * m + 2039 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3817.1, data_12_3817.2]

/-- Complete interval computation for depth 12, residue 3818. -/
theorem bounds_12_3818 : exactInterval 12 3818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3818 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3818) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3818 : oddCount 3818 12 = 4 ∧ acceleratedOrbit 12 3818 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3818 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3818) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3818.1, data_12_3818.2]

/-- Complete interval computation for depth 12, residue 3819. -/
theorem bounds_12_3819 : exactInterval 12 3819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3819 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3819) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3819 : oddCount 3819 12 = 6 ∧ acceleratedOrbit 12 3819 = 680 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3819 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3819) = 3 ^ 6 * m + 680 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3819.1, data_12_3819.2]

/-- Complete interval computation for depth 12, residue 3820. -/
theorem bounds_12_3820 : exactInterval 12 3820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3820 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3820) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3820 : oddCount 3820 12 = 5 ∧ acceleratedOrbit 12 3820 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3820 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3820) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3820.1, data_12_3820.2]

/-- Complete interval computation for depth 12, residue 3821. -/
theorem bounds_12_3821 : exactInterval 12 3821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3821 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3821) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3821 : oddCount 3821 12 = 5 ∧ acceleratedOrbit 12 3821 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3821 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3821) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3821.1, data_12_3821.2]

/-- Complete interval computation for depth 12, residue 3822. -/
theorem bounds_12_3822 : exactInterval 12 3822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3822 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3822) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3822 : oddCount 3822 12 = 5 ∧ acceleratedOrbit 12 3822 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3822 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3822) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3822.1, data_12_3822.2]

/-- Complete interval computation for depth 12, residue 3823. -/
theorem bounds_12_3823 : exactInterval 12 3823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_3823 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 3823) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_3823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_3823 : oddCount 3823 12 = 9 ∧ acceleratedOrbit 12 3823 = 18377 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_3823 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 3823) = 3 ^ 9 * m + 18377 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_3823.1, data_12_3823.2]

end Collatz.Research.StoppingAtlas.Batch0449
