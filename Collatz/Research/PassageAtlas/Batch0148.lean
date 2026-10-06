import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0148

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 4816. -/
theorem bounds_15_4816 : exactInterval 15 4816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4816 : oddCount 4816 15 = 3 ∧ acceleratedOrbit 15 4816 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4816) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4816.1, data_15_4816.2]

/-- Complete interval computation for depth 15, residue 4817. -/
theorem bounds_15_4817 : exactInterval 15 4817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4817 : oddCount 4817 15 = 7 ∧ acceleratedOrbit 15 4817 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4817) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4817.1, data_15_4817.2]

/-- Complete interval computation for depth 15, residue 4818. -/
theorem bounds_15_4818 : exactInterval 15 4818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4818 : oddCount 4818 15 = 7 ∧ acceleratedOrbit 15 4818 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4818) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4818.1, data_15_4818.2]

/-- Complete interval computation for depth 15, residue 4819. -/
theorem bounds_15_4819 : exactInterval 15 4819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4819 : oddCount 4819 15 = 7 ∧ acceleratedOrbit 15 4819 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4819) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4819.1, data_15_4819.2]

/-- Complete interval computation for depth 15, residue 4820. -/
theorem bounds_15_4820 : exactInterval 15 4820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4820 : oddCount 4820 15 = 3 ∧ acceleratedOrbit 15 4820 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4820) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4820.1, data_15_4820.2]

/-- Complete interval computation for depth 15, residue 4821. -/
theorem bounds_15_4821 : exactInterval 15 4821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4821 : oddCount 4821 15 = 3 ∧ acceleratedOrbit 15 4821 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4821) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4821.1, data_15_4821.2]

/-- Complete interval computation for depth 15, residue 4822. -/
theorem bounds_15_4822 : exactInterval 15 4822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4822 : oddCount 4822 15 = 8 ∧ acceleratedOrbit 15 4822 = 967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4822) = 3 ^ 8 * m + 967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4822.1, data_15_4822.2]

/-- Complete interval computation for depth 15, residue 4823. -/
theorem bounds_15_4823 : exactInterval 15 4823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4823 : oddCount 4823 15 = 8 ∧ acceleratedOrbit 15 4823 = 967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4823) = 3 ^ 8 * m + 967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4823.1, data_15_4823.2]

/-- Complete interval computation for depth 15, residue 4824. -/
theorem bounds_15_4824 : exactInterval 15 4824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4824 : oddCount 4824 15 = 9 ∧ acceleratedOrbit 15 4824 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4824) = 3 ^ 9 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4824.1, data_15_4824.2]

/-- Complete interval computation for depth 15, residue 4825. -/
theorem bounds_15_4825 : exactInterval 15 4825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4825 : oddCount 4825 15 = 8 ∧ acceleratedOrbit 15 4825 = 971 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4825) = 3 ^ 8 * m + 971 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4825.1, data_15_4825.2]

/-- Complete interval computation for depth 15, residue 4826. -/
theorem bounds_15_4826 : exactInterval 15 4826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4826 : oddCount 4826 15 = 9 ∧ acceleratedOrbit 15 4826 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4826) = 3 ^ 9 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4826.1, data_15_4826.2]

/-- Complete interval computation for depth 15, residue 4827. -/
theorem bounds_15_4827 : exactInterval 15 4827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4827 : oddCount 4827 15 = 11 ∧ acceleratedOrbit 15 4827 = 26108 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4827) = 3 ^ 11 * m + 26108 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4827.1, data_15_4827.2]

/-- Complete interval computation for depth 15, residue 4828. -/
theorem bounds_15_4828 : exactInterval 15 4828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4828 : oddCount 4828 15 = 9 ∧ acceleratedOrbit 15 4828 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4828) = 3 ^ 9 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4828.1, data_15_4828.2]

/-- Complete interval computation for depth 15, residue 4829. -/
theorem bounds_15_4829 : exactInterval 15 4829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4829 : oddCount 4829 15 = 9 ∧ acceleratedOrbit 15 4829 = 2906 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4829) = 3 ^ 9 * m + 2906 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4829.1, data_15_4829.2]

/-- Complete interval computation for depth 15, residue 4830. -/
theorem bounds_15_4830 : exactInterval 15 4830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4830 : oddCount 4830 15 = 7 ∧ acceleratedOrbit 15 4830 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4830) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4830.1, data_15_4830.2]

/-- Complete interval computation for depth 15, residue 4831. -/
theorem bounds_15_4831 : exactInterval 15 4831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4831 : oddCount 4831 15 = 7 ∧ acceleratedOrbit 15 4831 = 323 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4831) = 3 ^ 7 * m + 323 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4831.1, data_15_4831.2]

/-- Complete interval computation for depth 15, residue 4832. -/
theorem bounds_15_4832 : exactInterval 15 4832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4832 : oddCount 4832 15 = 3 ∧ acceleratedOrbit 15 4832 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4832) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4832.1, data_15_4832.2]

/-- Complete interval computation for depth 15, residue 4833. -/
theorem bounds_15_4833 : exactInterval 15 4833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4833 : oddCount 4833 15 = 10 ∧ acceleratedOrbit 15 4833 = 8714 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4833) = 3 ^ 10 * m + 8714 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4833.1, data_15_4833.2]

/-- Complete interval computation for depth 15, residue 4834. -/
theorem bounds_15_4834 : exactInterval 15 4834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4834 : oddCount 4834 15 = 3 ∧ acceleratedOrbit 15 4834 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4834) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4834.1, data_15_4834.2]

/-- Complete interval computation for depth 15, residue 4835. -/
theorem bounds_15_4835 : exactInterval 15 4835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4835 : oddCount 4835 15 = 3 ∧ acceleratedOrbit 15 4835 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4835) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4835.1, data_15_4835.2]

/-- Complete interval computation for depth 15, residue 4836. -/
theorem bounds_15_4836 : exactInterval 15 4836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4836 : oddCount 4836 15 = 9 ∧ acceleratedOrbit 15 4836 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4836) = 3 ^ 9 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4836.1, data_15_4836.2]

/-- Complete interval computation for depth 15, residue 4837. -/
theorem bounds_15_4837 : exactInterval 15 4837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4837 : oddCount 4837 15 = 9 ∧ acceleratedOrbit 15 4837 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4837) = 3 ^ 9 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4837.1, data_15_4837.2]

/-- Complete interval computation for depth 15, residue 4838. -/
theorem bounds_15_4838 : exactInterval 15 4838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4838 : oddCount 4838 15 = 9 ∧ acceleratedOrbit 15 4838 = 2915 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4838) = 3 ^ 9 * m + 2915 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4838.1, data_15_4838.2]

/-- Complete interval computation for depth 15, residue 4839. -/
theorem bounds_15_4839 : exactInterval 15 4839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4839 : oddCount 4839 15 = 10 ∧ acceleratedOrbit 15 4839 = 8723 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4839) = 3 ^ 10 * m + 8723 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4839.1, data_15_4839.2]

/-- Complete interval computation for depth 15, residue 4840. -/
theorem bounds_15_4840 : exactInterval 15 4840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4840 : oddCount 4840 15 = 3 ∧ acceleratedOrbit 15 4840 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4840) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4840.1, data_15_4840.2]

/-- Complete interval computation for depth 15, residue 4841. -/
theorem bounds_15_4841 : exactInterval 15 4841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4841 : oddCount 4841 15 = 11 ∧ acceleratedOrbit 15 4841 = 26183 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4841) = 3 ^ 11 * m + 26183 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4841.1, data_15_4841.2]

/-- Complete interval computation for depth 15, residue 4842. -/
theorem bounds_15_4842 : exactInterval 15 4842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4842 : oddCount 4842 15 = 3 ∧ acceleratedOrbit 15 4842 = 4 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4842) = 3 ^ 3 * m + 4 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4842.1, data_15_4842.2]

/-- Complete interval computation for depth 15, residue 4843. -/
theorem bounds_15_4843 : exactInterval 15 4843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4843 : oddCount 4843 15 = 9 ∧ acceleratedOrbit 15 4843 = 2911 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4843) = 3 ^ 9 * m + 2911 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4843.1, data_15_4843.2]

/-- Complete interval computation for depth 15, residue 4844. -/
theorem bounds_15_4844 : exactInterval 15 4844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4844 : oddCount 4844 15 = 10 ∧ acceleratedOrbit 15 4844 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4844) = 3 ^ 10 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4844.1, data_15_4844.2]

/-- Complete interval computation for depth 15, residue 4845. -/
theorem bounds_15_4845 : exactInterval 15 4845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4845 : oddCount 4845 15 = 10 ∧ acceleratedOrbit 15 4845 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4845) = 3 ^ 10 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4845.1, data_15_4845.2]

/-- Complete interval computation for depth 15, residue 4846. -/
theorem bounds_15_4846 : exactInterval 15 4846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4846 : oddCount 4846 15 = 10 ∧ acceleratedOrbit 15 4846 = 8747 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4846) = 3 ^ 10 * m + 8747 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4846.1, data_15_4846.2]

/-- Complete interval computation for depth 15, residue 4847. -/
theorem bounds_15_4847 : exactInterval 15 4847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4847 : oddCount 4847 15 = 11 ∧ acceleratedOrbit 15 4847 = 26210 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4847) = 3 ^ 11 * m + 26210 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4847.1, data_15_4847.2]

/-- Complete interval computation for depth 15, residue 4848. -/
theorem bounds_15_4848 : exactInterval 15 4848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_4848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 4848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_4848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_4848 : oddCount 4848 15 = 7 ∧ acceleratedOrbit 15 4848 = 325 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_4848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 4848) = 3 ^ 7 * m + 325 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_4848.1, data_15_4848.2]

end Collatz.Research.PassageAtlas.Batch0148
