import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0636

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20807. -/
theorem bounds_15_20807 : exactInterval 15 20807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20807 : oddCount 20807 15 = 10 ∧ acceleratedOrbit 15 20807 = 37498 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20807) = 3 ^ 10 * m + 37498 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20807.1, data_15_20807.2]

/-- Complete interval computation for depth 15, residue 20808. -/
theorem bounds_15_20808 : exactInterval 15 20808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20808 : oddCount 20808 15 = 8 ∧ acceleratedOrbit 15 20808 = 4169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20808) = 3 ^ 8 * m + 4169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20808.1, data_15_20808.2]

/-- Complete interval computation for depth 15, residue 20809. -/
theorem bounds_15_20809 : exactInterval 15 20809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20809 : oddCount 20809 15 = 6 ∧ acceleratedOrbit 15 20809 = 463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20809) = 3 ^ 6 * m + 463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20809.1, data_15_20809.2]

/-- Complete interval computation for depth 15, residue 20810. -/
theorem bounds_15_20810 : exactInterval 15 20810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20810 : oddCount 20810 15 = 8 ∧ acceleratedOrbit 15 20810 = 4169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20810) = 3 ^ 8 * m + 4169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20810.1, data_15_20810.2]

/-- Complete interval computation for depth 15, residue 20811. -/
theorem bounds_15_20811 : exactInterval 15 20811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20811 : oddCount 20811 15 = 7 ∧ acceleratedOrbit 15 20811 = 1390 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20811) = 3 ^ 7 * m + 1390 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20811.1, data_15_20811.2]

/-- Complete interval computation for depth 15, residue 20812. -/
theorem bounds_15_20812 : exactInterval 15 20812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20812 : oddCount 20812 15 = 8 ∧ acceleratedOrbit 15 20812 = 4169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20812) = 3 ^ 8 * m + 4169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20812.1, data_15_20812.2]

/-- Complete interval computation for depth 15, residue 20813. -/
theorem bounds_15_20813 : exactInterval 15 20813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20813 : oddCount 20813 15 = 8 ∧ acceleratedOrbit 15 20813 = 4169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20813) = 3 ^ 8 * m + 4169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20813.1, data_15_20813.2]

/-- Complete interval computation for depth 15, residue 20814. -/
theorem bounds_15_20814 : exactInterval 15 20814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20814 : oddCount 20814 15 = 10 ∧ acceleratedOrbit 15 20814 = 37513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20814) = 3 ^ 10 * m + 37513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20814.1, data_15_20814.2]

/-- Complete interval computation for depth 15, residue 20815. -/
theorem bounds_15_20815 : exactInterval 15 20815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20815 : oddCount 20815 15 = 10 ∧ acceleratedOrbit 15 20815 = 37513 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20815) = 3 ^ 10 * m + 37513 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20815.1, data_15_20815.2]

/-- Complete interval computation for depth 15, residue 20816. -/
theorem bounds_15_20816 : exactInterval 15 20816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20816 : oddCount 20816 15 = 4 ∧ acceleratedOrbit 15 20816 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20816) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20816.1, data_15_20816.2]

/-- Complete interval computation for depth 15, residue 20817. -/
theorem bounds_15_20817 : exactInterval 15 20817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20817 : oddCount 20817 15 = 8 ∧ acceleratedOrbit 15 20817 = 4169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20817) = 3 ^ 8 * m + 4169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20817.1, data_15_20817.2]

/-- Complete interval computation for depth 15, residue 20818. -/
theorem bounds_15_20818 : exactInterval 15 20818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20818 : oddCount 20818 15 = 12 ∧ acceleratedOrbit 15 20818 = 337688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20818) = 3 ^ 12 * m + 337688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20818.1, data_15_20818.2]

/-- Complete interval computation for depth 15, residue 20819. -/
theorem bounds_15_20819 : exactInterval 15 20819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20819 : oddCount 20819 15 = 12 ∧ acceleratedOrbit 15 20819 = 337688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20819) = 3 ^ 12 * m + 337688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20819.1, data_15_20819.2]

/-- Complete interval computation for depth 15, residue 20820. -/
theorem bounds_15_20820 : exactInterval 15 20820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20820 : oddCount 20820 15 = 4 ∧ acceleratedOrbit 15 20820 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20820) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20820.1, data_15_20820.2]

/-- Complete interval computation for depth 15, residue 20821. -/
theorem bounds_15_20821 : exactInterval 15 20821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20821 : oddCount 20821 15 = 4 ∧ acceleratedOrbit 15 20821 = 53 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20821) = 3 ^ 4 * m + 53 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20821.1, data_15_20821.2]

/-- Complete interval computation for depth 15, residue 20822. -/
theorem bounds_15_20822 : exactInterval 15 20822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20822 : oddCount 20822 15 = 8 ∧ acceleratedOrbit 15 20822 = 4171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20822) = 3 ^ 8 * m + 4171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20822.1, data_15_20822.2]

/-- Complete interval computation for depth 15, residue 20823. -/
theorem bounds_15_20823 : exactInterval 15 20823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20823 : oddCount 20823 15 = 8 ∧ acceleratedOrbit 15 20823 = 4171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20823) = 3 ^ 8 * m + 4171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20823.1, data_15_20823.2]

/-- Complete interval computation for depth 15, residue 20824. -/
theorem bounds_15_20824 : exactInterval 15 20824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20824 : oddCount 20824 15 = 5 ∧ acceleratedOrbit 15 20824 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20824) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20824.1, data_15_20824.2]

/-- Complete interval computation for depth 15, residue 20825. -/
theorem bounds_15_20825 : exactInterval 15 20825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20825 : oddCount 20825 15 = 9 ∧ acceleratedOrbit 15 20825 = 12514 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20825) = 3 ^ 9 * m + 12514 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20825.1, data_15_20825.2]

/-- Complete interval computation for depth 15, residue 20826. -/
theorem bounds_15_20826 : exactInterval 15 20826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20826 : oddCount 20826 15 = 5 ∧ acceleratedOrbit 15 20826 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20826) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20826.1, data_15_20826.2]

/-- Complete interval computation for depth 15, residue 20827. -/
theorem bounds_15_20827 : exactInterval 15 20827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20827 : oddCount 20827 15 = 8 ∧ acceleratedOrbit 15 20827 = 4171 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20827) = 3 ^ 8 * m + 4171 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20827.1, data_15_20827.2]

/-- Complete interval computation for depth 15, residue 20828. -/
theorem bounds_15_20828 : exactInterval 15 20828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20828 : oddCount 20828 15 = 5 ∧ acceleratedOrbit 15 20828 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20828) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20828.1, data_15_20828.2]

/-- Complete interval computation for depth 15, residue 20829. -/
theorem bounds_15_20829 : exactInterval 15 20829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20829 : oddCount 20829 15 = 5 ∧ acceleratedOrbit 15 20829 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20829) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20829.1, data_15_20829.2]

/-- Complete interval computation for depth 15, residue 20830. -/
theorem bounds_15_20830 : exactInterval 15 20830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20830 : oddCount 20830 15 = 10 ∧ acceleratedOrbit 15 20830 = 37543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20830) = 3 ^ 10 * m + 37543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20830.1, data_15_20830.2]

/-- Complete interval computation for depth 15, residue 20831. -/
theorem bounds_15_20831 : exactInterval 15 20831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20831 : oddCount 20831 15 = 10 ∧ acceleratedOrbit 15 20831 = 37543 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20831) = 3 ^ 10 * m + 37543 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20831.1, data_15_20831.2]

/-- Complete interval computation for depth 15, residue 20832. -/
theorem bounds_15_20832 : exactInterval 15 20832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20832 : oddCount 20832 15 = 5 ∧ acceleratedOrbit 15 20832 = 155 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20832) = 3 ^ 5 * m + 155 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20832.1, data_15_20832.2]

/-- Complete interval computation for depth 15, residue 20833. -/
theorem bounds_15_20833 : exactInterval 15 20833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20833 : oddCount 20833 15 = 8 ∧ acceleratedOrbit 15 20833 = 4172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20833) = 3 ^ 8 * m + 4172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20833.1, data_15_20833.2]

/-- Complete interval computation for depth 15, residue 20834. -/
theorem bounds_15_20834 : exactInterval 15 20834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20834 : oddCount 20834 15 = 6 ∧ acceleratedOrbit 15 20834 = 464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20834) = 3 ^ 6 * m + 464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20834.1, data_15_20834.2]

/-- Complete interval computation for depth 15, residue 20835. -/
theorem bounds_15_20835 : exactInterval 15 20835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20835 : oddCount 20835 15 = 6 ∧ acceleratedOrbit 15 20835 = 464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20835) = 3 ^ 6 * m + 464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20835.1, data_15_20835.2]

/-- Complete interval computation for depth 15, residue 20836. -/
theorem bounds_15_20836 : exactInterval 15 20836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20836 : oddCount 20836 15 = 6 ∧ acceleratedOrbit 15 20836 = 464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20836) = 3 ^ 6 * m + 464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20836.1, data_15_20836.2]

/-- Complete interval computation for depth 15, residue 20837. -/
theorem bounds_15_20837 : exactInterval 15 20837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20837 : oddCount 20837 15 = 6 ∧ acceleratedOrbit 15 20837 = 464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20837) = 3 ^ 6 * m + 464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20837.1, data_15_20837.2]

/-- Complete interval computation for depth 15, residue 20838. -/
theorem bounds_15_20838 : exactInterval 15 20838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20838 : oddCount 20838 15 = 6 ∧ acceleratedOrbit 15 20838 = 464 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20838) = 3 ^ 6 * m + 464 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20838.1, data_15_20838.2]

/-- Complete interval computation for depth 15, residue 20839. -/
theorem bounds_15_20839 : exactInterval 15 20839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20839 : oddCount 20839 15 = 10 ∧ acceleratedOrbit 15 20839 = 37556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20839) = 3 ^ 10 * m + 37556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20839.1, data_15_20839.2]

end Collatz.Research.PassageAtlas.Batch0636
