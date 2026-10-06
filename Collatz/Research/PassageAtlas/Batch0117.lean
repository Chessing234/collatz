import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0117

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 3801. -/
theorem bounds_15_3801 : exactInterval 15 3801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3801 : oddCount 3801 15 = 6 ∧ acceleratedOrbit 15 3801 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3801) = 3 ^ 6 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3801.1, data_15_3801.2]

/-- Complete interval computation for depth 15, residue 3802. -/
theorem bounds_15_3802 : exactInterval 15 3802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3802 : oddCount 3802 15 = 6 ∧ acceleratedOrbit 15 3802 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3802) = 3 ^ 6 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3802.1, data_15_3802.2]

/-- Complete interval computation for depth 15, residue 3803. -/
theorem bounds_15_3803 : exactInterval 15 3803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3803 : oddCount 3803 15 = 11 ∧ acceleratedOrbit 15 3803 = 20573 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3803) = 3 ^ 11 * m + 20573 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3803.1, data_15_3803.2]

/-- Complete interval computation for depth 15, residue 3804. -/
theorem bounds_15_3804 : exactInterval 15 3804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3804 : oddCount 3804 15 = 6 ∧ acceleratedOrbit 15 3804 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3804) = 3 ^ 6 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3804.1, data_15_3804.2]

/-- Complete interval computation for depth 15, residue 3805. -/
theorem bounds_15_3805 : exactInterval 15 3805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3805 : oddCount 3805 15 = 6 ∧ acceleratedOrbit 15 3805 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3805) = 3 ^ 6 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3805.1, data_15_3805.2]

/-- Complete interval computation for depth 15, residue 3806. -/
theorem bounds_15_3806 : exactInterval 15 3806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3806 : oddCount 3806 15 = 9 ∧ acceleratedOrbit 15 3806 = 2288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3806) = 3 ^ 9 * m + 2288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3806.1, data_15_3806.2]

/-- Complete interval computation for depth 15, residue 3807. -/
theorem bounds_15_3807 : exactInterval 15 3807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3807 : oddCount 3807 15 = 9 ∧ acceleratedOrbit 15 3807 = 2288 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3807) = 3 ^ 9 * m + 2288 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3807.1, data_15_3807.2]

/-- Complete interval computation for depth 15, residue 3808. -/
theorem bounds_15_3808 : exactInterval 15 3808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3808 : oddCount 3808 15 = 5 ∧ acceleratedOrbit 15 3808 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3808) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3808.1, data_15_3808.2]

/-- Complete interval computation for depth 15, residue 3809. -/
theorem bounds_15_3809 : exactInterval 15 3809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3809 : oddCount 3809 15 = 9 ∧ acceleratedOrbit 15 3809 = 2290 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3809) = 3 ^ 9 * m + 2290 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3809.1, data_15_3809.2]

/-- Complete interval computation for depth 15, residue 3810. -/
theorem bounds_15_3810 : exactInterval 15 3810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3810 : oddCount 3810 15 = 5 ∧ acceleratedOrbit 15 3810 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3810) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3810.1, data_15_3810.2]

/-- Complete interval computation for depth 15, residue 3811. -/
theorem bounds_15_3811 : exactInterval 15 3811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3811 : oddCount 3811 15 = 5 ∧ acceleratedOrbit 15 3811 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3811) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3811.1, data_15_3811.2]

/-- Complete interval computation for depth 15, residue 3812. -/
theorem bounds_15_3812 : exactInterval 15 3812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3812 : oddCount 3812 15 = 7 ∧ acceleratedOrbit 15 3812 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3812) = 3 ^ 7 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3812.1, data_15_3812.2]

/-- Complete interval computation for depth 15, residue 3813. -/
theorem bounds_15_3813 : exactInterval 15 3813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3813 : oddCount 3813 15 = 7 ∧ acceleratedOrbit 15 3813 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3813) = 3 ^ 7 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3813.1, data_15_3813.2]

/-- Complete interval computation for depth 15, residue 3814. -/
theorem bounds_15_3814 : exactInterval 15 3814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3814 : oddCount 3814 15 = 7 ∧ acceleratedOrbit 15 3814 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3814) = 3 ^ 7 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3814.1, data_15_3814.2]

/-- Complete interval computation for depth 15, residue 3815. -/
theorem bounds_15_3815 : exactInterval 15 3815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3815 : oddCount 3815 15 = 10 ∧ acceleratedOrbit 15 3815 = 6878 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3815) = 3 ^ 10 * m + 6878 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3815.1, data_15_3815.2]

/-- Complete interval computation for depth 15, residue 3816. -/
theorem bounds_15_3816 : exactInterval 15 3816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3816 : oddCount 3816 15 = 5 ∧ acceleratedOrbit 15 3816 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3816) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3816.1, data_15_3816.2]

/-- Complete interval computation for depth 15, residue 3817. -/
theorem bounds_15_3817 : exactInterval 15 3817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3817 : oddCount 3817 15 = 10 ∧ acceleratedOrbit 15 3817 = 6884 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3817) = 3 ^ 10 * m + 6884 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3817.1, data_15_3817.2]

/-- Complete interval computation for depth 15, residue 3818. -/
theorem bounds_15_3818 : exactInterval 15 3818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3818 : oddCount 3818 15 = 5 ∧ acceleratedOrbit 15 3818 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3818) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3818.1, data_15_3818.2]

/-- Complete interval computation for depth 15, residue 3819. -/
theorem bounds_15_3819 : exactInterval 15 3819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3819 : oddCount 3819 15 = 6 ∧ acceleratedOrbit 15 3819 = 85 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3819) = 3 ^ 6 * m + 85 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3819.1, data_15_3819.2]

/-- Complete interval computation for depth 15, residue 3820. -/
theorem bounds_15_3820 : exactInterval 15 3820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3820 : oddCount 3820 15 = 7 ∧ acceleratedOrbit 15 3820 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3820) = 3 ^ 7 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3820.1, data_15_3820.2]

/-- Complete interval computation for depth 15, residue 3821. -/
theorem bounds_15_3821 : exactInterval 15 3821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3821 : oddCount 3821 15 = 7 ∧ acceleratedOrbit 15 3821 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3821) = 3 ^ 7 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3821.1, data_15_3821.2]

/-- Complete interval computation for depth 15, residue 3822. -/
theorem bounds_15_3822 : exactInterval 15 3822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3822 : oddCount 3822 15 = 7 ∧ acceleratedOrbit 15 3822 = 256 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3822) = 3 ^ 7 * m + 256 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3822.1, data_15_3822.2]

/-- Complete interval computation for depth 15, residue 3823. -/
theorem bounds_15_3823 : exactInterval 15 3823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3823 : oddCount 3823 15 = 11 ∧ acceleratedOrbit 15 3823 = 20675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3823) = 3 ^ 11 * m + 20675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3823.1, data_15_3823.2]

/-- Complete interval computation for depth 15, residue 3824. -/
theorem bounds_15_3824 : exactInterval 15 3824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3824 : oddCount 3824 15 = 9 ∧ acceleratedOrbit 15 3824 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3824) = 3 ^ 9 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3824.1, data_15_3824.2]

/-- Complete interval computation for depth 15, residue 3825. -/
theorem bounds_15_3825 : exactInterval 15 3825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3825 : oddCount 3825 15 = 5 ∧ acceleratedOrbit 15 3825 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3825) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3825.1, data_15_3825.2]

/-- Complete interval computation for depth 15, residue 3826. -/
theorem bounds_15_3826 : exactInterval 15 3826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3826 : oddCount 3826 15 = 8 ∧ acceleratedOrbit 15 3826 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3826) = 3 ^ 8 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3826.1, data_15_3826.2]

/-- Complete interval computation for depth 15, residue 3827. -/
theorem bounds_15_3827 : exactInterval 15 3827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3827 : oddCount 3827 15 = 8 ∧ acceleratedOrbit 15 3827 = 767 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3827) = 3 ^ 8 * m + 767 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3827.1, data_15_3827.2]

/-- Complete interval computation for depth 15, residue 3828. -/
theorem bounds_15_3828 : exactInterval 15 3828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3828 : oddCount 3828 15 = 9 ∧ acceleratedOrbit 15 3828 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3828) = 3 ^ 9 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3828.1, data_15_3828.2]

/-- Complete interval computation for depth 15, residue 3829. -/
theorem bounds_15_3829 : exactInterval 15 3829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3829 : oddCount 3829 15 = 9 ∧ acceleratedOrbit 15 3829 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3829) = 3 ^ 9 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3829.1, data_15_3829.2]

/-- Complete interval computation for depth 15, residue 3830. -/
theorem bounds_15_3830 : exactInterval 15 3830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3830 : oddCount 3830 15 = 10 ∧ acceleratedOrbit 15 3830 = 6911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3830) = 3 ^ 10 * m + 6911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3830.1, data_15_3830.2]

/-- Complete interval computation for depth 15, residue 3831. -/
theorem bounds_15_3831 : exactInterval 15 3831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3831 : oddCount 3831 15 = 10 ∧ acceleratedOrbit 15 3831 = 6911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3831) = 3 ^ 10 * m + 6911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3831.1, data_15_3831.2]

/-- Complete interval computation for depth 15, residue 3832. -/
theorem bounds_15_3832 : exactInterval 15 3832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_3832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 3832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_3832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_3832 : oddCount 3832 15 = 9 ∧ acceleratedOrbit 15 3832 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_3832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 3832) = 3 ^ 9 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_3832.1, data_15_3832.2]

end Collatz.Research.PassageAtlas.Batch0117
