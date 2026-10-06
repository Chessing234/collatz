import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0758

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24805. -/
theorem bounds_15_24805 : exactInterval 15 24805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24805 : oddCount 24805 15 = 5 ∧ acceleratedOrbit 15 24805 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24805) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24805.1, data_15_24805.2]

/-- Complete interval computation for depth 15, residue 24806. -/
theorem bounds_15_24806 : exactInterval 15 24806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24806 : oddCount 24806 15 = 5 ∧ acceleratedOrbit 15 24806 = 184 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24806) = 3 ^ 5 * m + 184 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24806.1, data_15_24806.2]

/-- Complete interval computation for depth 15, residue 24807. -/
theorem bounds_15_24807 : exactInterval 15 24807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24807 : oddCount 24807 15 = 9 ∧ acceleratedOrbit 15 24807 = 14903 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24807) = 3 ^ 9 * m + 14903 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24807.1, data_15_24807.2]

/-- Complete interval computation for depth 15, residue 24808. -/
theorem bounds_15_24808 : exactInterval 15 24808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24808 : oddCount 24808 15 = 6 ∧ acceleratedOrbit 15 24808 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24808) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24808.1, data_15_24808.2]

/-- Complete interval computation for depth 15, residue 24809. -/
theorem bounds_15_24809 : exactInterval 15 24809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24809 : oddCount 24809 15 = 11 ∧ acceleratedOrbit 15 24809 = 134135 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24809) = 3 ^ 11 * m + 134135 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24809.1, data_15_24809.2]

/-- Complete interval computation for depth 15, residue 24810. -/
theorem bounds_15_24810 : exactInterval 15 24810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24810 : oddCount 24810 15 = 6 ∧ acceleratedOrbit 15 24810 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24810) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24810.1, data_15_24810.2]

/-- Complete interval computation for depth 15, residue 24811. -/
theorem bounds_15_24811 : exactInterval 15 24811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24811 : oddCount 24811 15 = 9 ∧ acceleratedOrbit 15 24811 = 14905 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24811) = 3 ^ 9 * m + 14905 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24811.1, data_15_24811.2]

/-- Complete interval computation for depth 15, residue 24812. -/
theorem bounds_15_24812 : exactInterval 15 24812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24812 : oddCount 24812 15 = 7 ∧ acceleratedOrbit 15 24812 = 1657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24812) = 3 ^ 7 * m + 1657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24812.1, data_15_24812.2]

/-- Complete interval computation for depth 15, residue 24813. -/
theorem bounds_15_24813 : exactInterval 15 24813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24813 : oddCount 24813 15 = 7 ∧ acceleratedOrbit 15 24813 = 1657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24813) = 3 ^ 7 * m + 1657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24813.1, data_15_24813.2]

/-- Complete interval computation for depth 15, residue 24814. -/
theorem bounds_15_24814 : exactInterval 15 24814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24814 : oddCount 24814 15 = 7 ∧ acceleratedOrbit 15 24814 = 1657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24814) = 3 ^ 7 * m + 1657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24814.1, data_15_24814.2]

/-- Complete interval computation for depth 15, residue 24815. -/
theorem bounds_15_24815 : exactInterval 15 24815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24815 : oddCount 24815 15 = 10 ∧ acceleratedOrbit 15 24815 = 44720 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24815) = 3 ^ 10 * m + 44720 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24815.1, data_15_24815.2]

/-- Complete interval computation for depth 15, residue 24816. -/
theorem bounds_15_24816 : exactInterval 15 24816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24816 : oddCount 24816 15 = 6 ∧ acceleratedOrbit 15 24816 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24816) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24816.1, data_15_24816.2]

/-- Complete interval computation for depth 15, residue 24817. -/
theorem bounds_15_24817 : exactInterval 15 24817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24817 : oddCount 24817 15 = 6 ∧ acceleratedOrbit 15 24817 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24817) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24817.1, data_15_24817.2]

/-- Complete interval computation for depth 15, residue 24818. -/
theorem bounds_15_24818 : exactInterval 15 24818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24818 : oddCount 24818 15 = 10 ∧ acceleratedOrbit 15 24818 = 44732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24818) = 3 ^ 10 * m + 44732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24818.1, data_15_24818.2]

/-- Complete interval computation for depth 15, residue 24819. -/
theorem bounds_15_24819 : exactInterval 15 24819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24819 : oddCount 24819 15 = 10 ∧ acceleratedOrbit 15 24819 = 44732 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24819) = 3 ^ 10 * m + 44732 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24819.1, data_15_24819.2]

/-- Complete interval computation for depth 15, residue 24820. -/
theorem bounds_15_24820 : exactInterval 15 24820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24820 : oddCount 24820 15 = 6 ∧ acceleratedOrbit 15 24820 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24820) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24820.1, data_15_24820.2]

/-- Complete interval computation for depth 15, residue 24821. -/
theorem bounds_15_24821 : exactInterval 15 24821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24821 : oddCount 24821 15 = 6 ∧ acceleratedOrbit 15 24821 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24821) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24821.1, data_15_24821.2]

/-- Complete interval computation for depth 15, residue 24822. -/
theorem bounds_15_24822 : exactInterval 15 24822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24822 : oddCount 24822 15 = 7 ∧ acceleratedOrbit 15 24822 = 1657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24822) = 3 ^ 7 * m + 1657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24822.1, data_15_24822.2]

/-- Complete interval computation for depth 15, residue 24823. -/
theorem bounds_15_24823 : exactInterval 15 24823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24823 : oddCount 24823 15 = 7 ∧ acceleratedOrbit 15 24823 = 1657 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24823) = 3 ^ 7 * m + 1657 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24823.1, data_15_24823.2]

/-- Complete interval computation for depth 15, residue 24824. -/
theorem bounds_15_24824 : exactInterval 15 24824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24824 : oddCount 24824 15 = 9 ∧ acceleratedOrbit 15 24824 = 14917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24824) = 3 ^ 9 * m + 14917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24824.1, data_15_24824.2]

/-- Complete interval computation for depth 15, residue 24825. -/
theorem bounds_15_24825 : exactInterval 15 24825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24825 : oddCount 24825 15 = 9 ∧ acceleratedOrbit 15 24825 = 14914 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24825) = 3 ^ 9 * m + 14914 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24825.1, data_15_24825.2]

/-- Complete interval computation for depth 15, residue 24826. -/
theorem bounds_15_24826 : exactInterval 15 24826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24826 : oddCount 24826 15 = 9 ∧ acceleratedOrbit 15 24826 = 14917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24826) = 3 ^ 9 * m + 14917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24826.1, data_15_24826.2]

/-- Complete interval computation for depth 15, residue 24827. -/
theorem bounds_15_24827 : exactInterval 15 24827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24827 : oddCount 24827 15 = 11 ∧ acceleratedOrbit 15 24827 = 134227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24827) = 3 ^ 11 * m + 134227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24827.1, data_15_24827.2]

/-- Complete interval computation for depth 15, residue 24828. -/
theorem bounds_15_24828 : exactInterval 15 24828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24828 : oddCount 24828 15 = 9 ∧ acceleratedOrbit 15 24828 = 14917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24828) = 3 ^ 9 * m + 14917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24828.1, data_15_24828.2]

/-- Complete interval computation for depth 15, residue 24829. -/
theorem bounds_15_24829 : exactInterval 15 24829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24829 : oddCount 24829 15 = 9 ∧ acceleratedOrbit 15 24829 = 14917 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24829) = 3 ^ 9 * m + 14917 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24829.1, data_15_24829.2]

/-- Complete interval computation for depth 15, residue 24830. -/
theorem bounds_15_24830 : exactInterval 15 24830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24830 : oddCount 24830 15 = 8 ∧ acceleratedOrbit 15 24830 = 4972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24830) = 3 ^ 8 * m + 4972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24830.1, data_15_24830.2]

/-- Complete interval computation for depth 15, residue 24831. -/
theorem bounds_15_24831 : exactInterval 15 24831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24831 : oddCount 24831 15 = 8 ∧ acceleratedOrbit 15 24831 = 4972 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24831) = 3 ^ 8 * m + 4972 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24831.1, data_15_24831.2]

/-- Complete interval computation for depth 15, residue 24832. -/
theorem bounds_15_24832 : exactInterval 15 24832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24832 : oddCount 24832 15 = 5 ∧ acceleratedOrbit 15 24832 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24832) = 3 ^ 5 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24832.1, data_15_24832.2]

/-- Complete interval computation for depth 15, residue 24833. -/
theorem bounds_15_24833 : exactInterval 15 24833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24833 : oddCount 24833 15 = 7 ∧ acceleratedOrbit 15 24833 = 1658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24833) = 3 ^ 7 * m + 1658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24833.1, data_15_24833.2]

/-- Complete interval computation for depth 15, residue 24834. -/
theorem bounds_15_24834 : exactInterval 15 24834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24834 : oddCount 24834 15 = 7 ∧ acceleratedOrbit 15 24834 = 1658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24834) = 3 ^ 7 * m + 1658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24834.1, data_15_24834.2]

/-- Complete interval computation for depth 15, residue 24835. -/
theorem bounds_15_24835 : exactInterval 15 24835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24835 : oddCount 24835 15 = 7 ∧ acceleratedOrbit 15 24835 = 1658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24835) = 3 ^ 7 * m + 1658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24835.1, data_15_24835.2]

/-- Complete interval computation for depth 15, residue 24836. -/
theorem bounds_15_24836 : exactInterval 15 24836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24836 : oddCount 24836 15 = 7 ∧ acceleratedOrbit 15 24836 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24836) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24836.1, data_15_24836.2]

/-- Complete interval computation for depth 15, residue 24837. -/
theorem bounds_15_24837 : exactInterval 15 24837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24837 : oddCount 24837 15 = 7 ∧ acceleratedOrbit 15 24837 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24837) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24837.1, data_15_24837.2]

end Collatz.Research.PassageAtlas.Batch0758
