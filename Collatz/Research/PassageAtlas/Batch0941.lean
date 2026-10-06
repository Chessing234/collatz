import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0941

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30801. -/
theorem bounds_15_30801 : exactInterval 15 30801 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30801 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30801) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30801 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30801 : oddCount 30801 15 = 8 ∧ acceleratedOrbit 15 30801 = 6169 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30801 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30801) = 3 ^ 8 * m + 6169 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30801.1, data_15_30801.2]

/-- Complete interval computation for depth 15, residue 30802. -/
theorem bounds_15_30802 : exactInterval 15 30802 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30802 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30802) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30802 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30802 : oddCount 30802 15 = 7 ∧ acceleratedOrbit 15 30802 = 2056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30802 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30802) = 3 ^ 7 * m + 2056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30802.1, data_15_30802.2]

/-- Complete interval computation for depth 15, residue 30803. -/
theorem bounds_15_30803 : exactInterval 15 30803 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30803 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30803) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30803 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30803 : oddCount 30803 15 = 7 ∧ acceleratedOrbit 15 30803 = 2056 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30803 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30803) = 3 ^ 7 * m + 2056 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30803.1, data_15_30803.2]

/-- Complete interval computation for depth 15, residue 30804. -/
theorem bounds_15_30804 : exactInterval 15 30804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30804 : oddCount 30804 15 = 6 ∧ acceleratedOrbit 15 30804 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30804) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30804.1, data_15_30804.2]

/-- Complete interval computation for depth 15, residue 30805. -/
theorem bounds_15_30805 : exactInterval 15 30805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30805 : oddCount 30805 15 = 6 ∧ acceleratedOrbit 15 30805 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30805) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30805.1, data_15_30805.2]

/-- Complete interval computation for depth 15, residue 30806. -/
theorem bounds_15_30806 : exactInterval 15 30806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30806 : oddCount 30806 15 = 6 ∧ acceleratedOrbit 15 30806 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30806) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30806.1, data_15_30806.2]

/-- Complete interval computation for depth 15, residue 30807. -/
theorem bounds_15_30807 : exactInterval 15 30807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30807 : oddCount 30807 15 = 6 ∧ acceleratedOrbit 15 30807 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30807) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30807.1, data_15_30807.2]

/-- Complete interval computation for depth 15, residue 30808. -/
theorem bounds_15_30808 : exactInterval 15 30808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30808 : oddCount 30808 15 = 6 ∧ acceleratedOrbit 15 30808 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30808) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30808.1, data_15_30808.2]

/-- Complete interval computation for depth 15, residue 30809. -/
theorem bounds_15_30809 : exactInterval 15 30809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30809 : oddCount 30809 15 = 6 ∧ acceleratedOrbit 15 30809 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30809) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30809.1, data_15_30809.2]

/-- Complete interval computation for depth 15, residue 30810. -/
theorem bounds_15_30810 : exactInterval 15 30810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30810 : oddCount 30810 15 = 6 ∧ acceleratedOrbit 15 30810 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30810) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30810.1, data_15_30810.2]

/-- Complete interval computation for depth 15, residue 30811. -/
theorem bounds_15_30811 : exactInterval 15 30811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30811 : oddCount 30811 15 = 12 ∧ acceleratedOrbit 15 30811 = 499729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30811) = 3 ^ 12 * m + 499729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30811.1, data_15_30811.2]

/-- Complete interval computation for depth 15, residue 30812. -/
theorem bounds_15_30812 : exactInterval 15 30812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30812 : oddCount 30812 15 = 6 ∧ acceleratedOrbit 15 30812 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30812) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30812.1, data_15_30812.2]

/-- Complete interval computation for depth 15, residue 30813. -/
theorem bounds_15_30813 : exactInterval 15 30813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30813 : oddCount 30813 15 = 6 ∧ acceleratedOrbit 15 30813 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30813) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30813.1, data_15_30813.2]

/-- Complete interval computation for depth 15, residue 30814. -/
theorem bounds_15_30814 : exactInterval 15 30814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30814 : oddCount 30814 15 = 9 ∧ acceleratedOrbit 15 30814 = 18512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30814) = 3 ^ 9 * m + 18512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30814.1, data_15_30814.2]

/-- Complete interval computation for depth 15, residue 30815. -/
theorem bounds_15_30815 : exactInterval 15 30815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30815 : oddCount 30815 15 = 9 ∧ acceleratedOrbit 15 30815 = 18512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30815) = 3 ^ 9 * m + 18512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30815.1, data_15_30815.2]

/-- Complete interval computation for depth 15, residue 30816. -/
theorem bounds_15_30816 : exactInterval 15 30816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30816 : oddCount 30816 15 = 6 ∧ acceleratedOrbit 15 30816 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30816) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30816.1, data_15_30816.2]

/-- Complete interval computation for depth 15, residue 30817. -/
theorem bounds_15_30817 : exactInterval 15 30817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30817 : oddCount 30817 15 = 7 ∧ acceleratedOrbit 15 30817 = 2057 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30817) = 3 ^ 7 * m + 2057 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30817.1, data_15_30817.2]

/-- Complete interval computation for depth 15, residue 30818. -/
theorem bounds_15_30818 : exactInterval 15 30818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30818 : oddCount 30818 15 = 6 ∧ acceleratedOrbit 15 30818 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30818) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30818.1, data_15_30818.2]

/-- Complete interval computation for depth 15, residue 30819. -/
theorem bounds_15_30819 : exactInterval 15 30819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30819 : oddCount 30819 15 = 6 ∧ acceleratedOrbit 15 30819 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30819) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30819.1, data_15_30819.2]

/-- Complete interval computation for depth 15, residue 30820. -/
theorem bounds_15_30820 : exactInterval 15 30820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30820 : oddCount 30820 15 = 6 ∧ acceleratedOrbit 15 30820 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30820) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30820.1, data_15_30820.2]

/-- Complete interval computation for depth 15, residue 30821. -/
theorem bounds_15_30821 : exactInterval 15 30821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30821 : oddCount 30821 15 = 6 ∧ acceleratedOrbit 15 30821 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30821) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30821.1, data_15_30821.2]

/-- Complete interval computation for depth 15, residue 30822. -/
theorem bounds_15_30822 : exactInterval 15 30822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30822 : oddCount 30822 15 = 6 ∧ acceleratedOrbit 15 30822 = 686 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30822) = 3 ^ 6 * m + 686 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30822.1, data_15_30822.2]

/-- Complete interval computation for depth 15, residue 30823. -/
theorem bounds_15_30823 : exactInterval 15 30823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30823 : oddCount 30823 15 = 10 ∧ acceleratedOrbit 15 30823 = 55547 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30823) = 3 ^ 10 * m + 55547 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30823.1, data_15_30823.2]

/-- Complete interval computation for depth 15, residue 30824. -/
theorem bounds_15_30824 : exactInterval 15 30824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30824 : oddCount 30824 15 = 6 ∧ acceleratedOrbit 15 30824 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30824) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30824.1, data_15_30824.2]

/-- Complete interval computation for depth 15, residue 30825. -/
theorem bounds_15_30825 : exactInterval 15 30825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30825 : oddCount 30825 15 = 8 ∧ acceleratedOrbit 15 30825 = 6173 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30825) = 3 ^ 8 * m + 6173 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30825.1, data_15_30825.2]

/-- Complete interval computation for depth 15, residue 30826. -/
theorem bounds_15_30826 : exactInterval 15 30826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30826 : oddCount 30826 15 = 6 ∧ acceleratedOrbit 15 30826 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30826) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30826.1, data_15_30826.2]

/-- Complete interval computation for depth 15, residue 30827. -/
theorem bounds_15_30827 : exactInterval 15 30827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30827 : oddCount 30827 15 = 10 ∧ acceleratedOrbit 15 30827 = 55556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30827) = 3 ^ 10 * m + 55556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30827.1, data_15_30827.2]

/-- Complete interval computation for depth 15, residue 30828. -/
theorem bounds_15_30828 : exactInterval 15 30828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30828 : oddCount 30828 15 = 10 ∧ acceleratedOrbit 15 30828 = 55565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30828) = 3 ^ 10 * m + 55565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30828.1, data_15_30828.2]

/-- Complete interval computation for depth 15, residue 30829. -/
theorem bounds_15_30829 : exactInterval 15 30829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30829 : oddCount 30829 15 = 10 ∧ acceleratedOrbit 15 30829 = 55565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30829) = 3 ^ 10 * m + 55565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30829.1, data_15_30829.2]

/-- Complete interval computation for depth 15, residue 30830. -/
theorem bounds_15_30830 : exactInterval 15 30830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30830 : oddCount 30830 15 = 10 ∧ acceleratedOrbit 15 30830 = 55565 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30830) = 3 ^ 10 * m + 55565 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30830.1, data_15_30830.2]

/-- Complete interval computation for depth 15, residue 30831. -/
theorem bounds_15_30831 : exactInterval 15 30831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30831 : oddCount 30831 15 = 10 ∧ acceleratedOrbit 15 30831 = 55561 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30831) = 3 ^ 10 * m + 55561 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30831.1, data_15_30831.2]

/-- Complete interval computation for depth 15, residue 30832. -/
theorem bounds_15_30832 : exactInterval 15 30832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30832 : oddCount 30832 15 = 5 ∧ acceleratedOrbit 15 30832 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30832) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30832.1, data_15_30832.2]

/-- Complete interval computation for depth 15, residue 30833. -/
theorem bounds_15_30833 : exactInterval 15 30833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30833 : oddCount 30833 15 = 6 ∧ acceleratedOrbit 15 30833 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30833) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30833.1, data_15_30833.2]

end Collatz.Research.PassageAtlas.Batch0941
