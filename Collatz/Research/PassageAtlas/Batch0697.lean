import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0697

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 22806. -/
theorem bounds_15_22806 : exactInterval 15 22806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22806 : oddCount 22806 15 = 7 ∧ acceleratedOrbit 15 22806 = 1523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22806) = 3 ^ 7 * m + 1523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22806.1, data_15_22806.2]

/-- Complete interval computation for depth 15, residue 22807. -/
theorem bounds_15_22807 : exactInterval 15 22807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22807 : oddCount 22807 15 = 7 ∧ acceleratedOrbit 15 22807 = 1523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22807) = 3 ^ 7 * m + 1523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22807.1, data_15_22807.2]

/-- Complete interval computation for depth 15, residue 22808. -/
theorem bounds_15_22808 : exactInterval 15 22808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22808 : oddCount 22808 15 = 5 ∧ acceleratedOrbit 15 22808 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22808) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22808.1, data_15_22808.2]

/-- Complete interval computation for depth 15, residue 22809. -/
theorem bounds_15_22809 : exactInterval 15 22809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22809 : oddCount 22809 15 = 7 ∧ acceleratedOrbit 15 22809 = 1523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22809) = 3 ^ 7 * m + 1523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22809.1, data_15_22809.2]

/-- Complete interval computation for depth 15, residue 22810. -/
theorem bounds_15_22810 : exactInterval 15 22810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22810 : oddCount 22810 15 = 5 ∧ acceleratedOrbit 15 22810 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22810) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22810.1, data_15_22810.2]

/-- Complete interval computation for depth 15, residue 22811. -/
theorem bounds_15_22811 : exactInterval 15 22811 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22811) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22811 : oddCount 22811 15 = 9 ∧ acceleratedOrbit 15 22811 = 13703 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22811) = 3 ^ 9 * m + 13703 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22811.1, data_15_22811.2]

/-- Complete interval computation for depth 15, residue 22812. -/
theorem bounds_15_22812 : exactInterval 15 22812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22812 : oddCount 22812 15 = 7 ∧ acceleratedOrbit 15 22812 = 1523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22812) = 3 ^ 7 * m + 1523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22812.1, data_15_22812.2]

/-- Complete interval computation for depth 15, residue 22813. -/
theorem bounds_15_22813 : exactInterval 15 22813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22813 : oddCount 22813 15 = 7 ∧ acceleratedOrbit 15 22813 = 1523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22813) = 3 ^ 7 * m + 1523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22813.1, data_15_22813.2]

/-- Complete interval computation for depth 15, residue 22814. -/
theorem bounds_15_22814 : exactInterval 15 22814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22814 : oddCount 22814 15 = 7 ∧ acceleratedOrbit 15 22814 = 1523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22814) = 3 ^ 7 * m + 1523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22814.1, data_15_22814.2]

/-- Complete interval computation for depth 15, residue 22815. -/
theorem bounds_15_22815 : exactInterval 15 22815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22815 : oddCount 22815 15 = 9 ∧ acceleratedOrbit 15 22815 = 13706 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22815) = 3 ^ 9 * m + 13706 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22815.1, data_15_22815.2]

/-- Complete interval computation for depth 15, residue 22816. -/
theorem bounds_15_22816 : exactInterval 15 22816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22816 : oddCount 22816 15 = 5 ∧ acceleratedOrbit 15 22816 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22816) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22816.1, data_15_22816.2]

/-- Complete interval computation for depth 15, residue 22817. -/
theorem bounds_15_22817 : exactInterval 15 22817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22817 : oddCount 22817 15 = 6 ∧ acceleratedOrbit 15 22817 = 508 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22817) = 3 ^ 6 * m + 508 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22817.1, data_15_22817.2]

/-- Complete interval computation for depth 15, residue 22818. -/
theorem bounds_15_22818 : exactInterval 15 22818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22818 : oddCount 22818 15 = 9 ∧ acceleratedOrbit 15 22818 = 13715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22818) = 3 ^ 9 * m + 13715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22818.1, data_15_22818.2]

/-- Complete interval computation for depth 15, residue 22819. -/
theorem bounds_15_22819 : exactInterval 15 22819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22819 : oddCount 22819 15 = 9 ∧ acceleratedOrbit 15 22819 = 13715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22819) = 3 ^ 9 * m + 13715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22819.1, data_15_22819.2]

/-- Complete interval computation for depth 15, residue 22820. -/
theorem bounds_15_22820 : exactInterval 15 22820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22820 : oddCount 22820 15 = 9 ∧ acceleratedOrbit 15 22820 = 13715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22820) = 3 ^ 9 * m + 13715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22820.1, data_15_22820.2]

/-- Complete interval computation for depth 15, residue 22821. -/
theorem bounds_15_22821 : exactInterval 15 22821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22821 : oddCount 22821 15 = 9 ∧ acceleratedOrbit 15 22821 = 13715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22821) = 3 ^ 9 * m + 13715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22821.1, data_15_22821.2]

/-- Complete interval computation for depth 15, residue 22822. -/
theorem bounds_15_22822 : exactInterval 15 22822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22822 : oddCount 22822 15 = 9 ∧ acceleratedOrbit 15 22822 = 13715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22822) = 3 ^ 9 * m + 13715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22822.1, data_15_22822.2]

/-- Complete interval computation for depth 15, residue 22823. -/
theorem bounds_15_22823 : exactInterval 15 22823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22823 : oddCount 22823 15 = 9 ∧ acceleratedOrbit 15 22823 = 13711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22823) = 3 ^ 9 * m + 13711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22823.1, data_15_22823.2]

/-- Complete interval computation for depth 15, residue 22824. -/
theorem bounds_15_22824 : exactInterval 15 22824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22824 : oddCount 22824 15 = 5 ∧ acceleratedOrbit 15 22824 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22824) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22824.1, data_15_22824.2]

/-- Complete interval computation for depth 15, residue 22825. -/
theorem bounds_15_22825 : exactInterval 15 22825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22825 : oddCount 22825 15 = 8 ∧ acceleratedOrbit 15 22825 = 4571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22825) = 3 ^ 8 * m + 4571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22825.1, data_15_22825.2]

/-- Complete interval computation for depth 15, residue 22826. -/
theorem bounds_15_22826 : exactInterval 15 22826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22826 : oddCount 22826 15 = 5 ∧ acceleratedOrbit 15 22826 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22826) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22826.1, data_15_22826.2]

/-- Complete interval computation for depth 15, residue 22827. -/
theorem bounds_15_22827 : exactInterval 15 22827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22827 : oddCount 22827 15 = 9 ∧ acceleratedOrbit 15 22827 = 13715 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22827) = 3 ^ 9 * m + 13715 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22827.1, data_15_22827.2]

/-- Complete interval computation for depth 15, residue 22828. -/
theorem bounds_15_22828 : exactInterval 15 22828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22828 : oddCount 22828 15 = 5 ∧ acceleratedOrbit 15 22828 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22828) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22828.1, data_15_22828.2]

/-- Complete interval computation for depth 15, residue 22829. -/
theorem bounds_15_22829 : exactInterval 15 22829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22829 : oddCount 22829 15 = 5 ∧ acceleratedOrbit 15 22829 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22829) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22829.1, data_15_22829.2]

/-- Complete interval computation for depth 15, residue 22830. -/
theorem bounds_15_22830 : exactInterval 15 22830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22830 : oddCount 22830 15 = 5 ∧ acceleratedOrbit 15 22830 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22830) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22830.1, data_15_22830.2]

/-- Complete interval computation for depth 15, residue 22831. -/
theorem bounds_15_22831 : exactInterval 15 22831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22831 : oddCount 22831 15 = 10 ∧ acceleratedOrbit 15 22831 = 41147 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22831) = 3 ^ 10 * m + 41147 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22831.1, data_15_22831.2]

/-- Complete interval computation for depth 15, residue 22832. -/
theorem bounds_15_22832 : exactInterval 15 22832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22832 : oddCount 22832 15 = 5 ∧ acceleratedOrbit 15 22832 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22832) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22832.1, data_15_22832.2]

/-- Complete interval computation for depth 15, residue 22833. -/
theorem bounds_15_22833 : exactInterval 15 22833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22833 : oddCount 22833 15 = 7 ∧ acceleratedOrbit 15 22833 = 1525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22833) = 3 ^ 7 * m + 1525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22833.1, data_15_22833.2]

/-- Complete interval computation for depth 15, residue 22834. -/
theorem bounds_15_22834 : exactInterval 15 22834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22834 : oddCount 22834 15 = 7 ∧ acceleratedOrbit 15 22834 = 1525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22834) = 3 ^ 7 * m + 1525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22834.1, data_15_22834.2]

/-- Complete interval computation for depth 15, residue 22835. -/
theorem bounds_15_22835 : exactInterval 15 22835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22835 : oddCount 22835 15 = 7 ∧ acceleratedOrbit 15 22835 = 1525 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22835) = 3 ^ 7 * m + 1525 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22835.1, data_15_22835.2]

/-- Complete interval computation for depth 15, residue 22836. -/
theorem bounds_15_22836 : exactInterval 15 22836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22836 : oddCount 22836 15 = 5 ∧ acceleratedOrbit 15 22836 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22836) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22836.1, data_15_22836.2]

/-- Complete interval computation for depth 15, residue 22837. -/
theorem bounds_15_22837 : exactInterval 15 22837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22837 : oddCount 22837 15 = 5 ∧ acceleratedOrbit 15 22837 = 170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22837) = 3 ^ 5 * m + 170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22837.1, data_15_22837.2]

/-- Complete interval computation for depth 15, residue 22838. -/
theorem bounds_15_22838 : exactInterval 15 22838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_22838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 22838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_22838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_22838 : oddCount 22838 15 = 10 ∧ acceleratedOrbit 15 22838 = 41161 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_22838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 22838) = 3 ^ 10 * m + 41161 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_22838.1, data_15_22838.2]

end Collatz.Research.PassageAtlas.Batch0697
