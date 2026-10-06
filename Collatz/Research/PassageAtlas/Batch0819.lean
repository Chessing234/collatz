import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0819

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 26804. -/
theorem bounds_15_26804 : exactInterval 15 26804 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26804 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26804) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26804 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26804 : oddCount 26804 15 = 5 ∧ acceleratedOrbit 15 26804 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26804 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26804) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26804.1, data_15_26804.2]

/-- Complete interval computation for depth 15, residue 26805. -/
theorem bounds_15_26805 : exactInterval 15 26805 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26805 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26805) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26805 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26805 : oddCount 26805 15 = 5 ∧ acceleratedOrbit 15 26805 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26805 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26805) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26805.1, data_15_26805.2]

/-- Complete interval computation for depth 15, residue 26806. -/
theorem bounds_15_26806 : exactInterval 15 26806 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26806 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26806) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26806 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26806 : oddCount 26806 15 = 11 ∧ acceleratedOrbit 15 26806 = 144935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26806 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26806) = 3 ^ 11 * m + 144935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26806.1, data_15_26806.2]

/-- Complete interval computation for depth 15, residue 26807. -/
theorem bounds_15_26807 : exactInterval 15 26807 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26807 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26807) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26807 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26807 : oddCount 26807 15 = 11 ∧ acceleratedOrbit 15 26807 = 144935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26807 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26807) = 3 ^ 11 * m + 144935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26807.1, data_15_26807.2]

/-- Complete interval computation for depth 15, residue 26808. -/
theorem bounds_15_26808 : exactInterval 15 26808 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26808 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26808) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26808 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26808 : oddCount 26808 15 = 5 ∧ acceleratedOrbit 15 26808 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26808 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26808) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26808.1, data_15_26808.2]

/-- Complete interval computation for depth 15, residue 26809. -/
theorem bounds_15_26809 : exactInterval 15 26809 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26809 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26809) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26809 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26809 : oddCount 26809 15 = 7 ∧ acceleratedOrbit 15 26809 = 1790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26809 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26809) = 3 ^ 7 * m + 1790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26809.1, data_15_26809.2]

/-- Complete interval computation for depth 15, residue 26810. -/
theorem bounds_15_26810 : exactInterval 15 26810 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26810 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26810) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26810 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26810 : oddCount 26810 15 = 5 ∧ acceleratedOrbit 15 26810 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26810 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26810) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26810.1, data_15_26810.2]

/-- Complete interval computation for depth 15, residue 26811. -/
theorem bounds_15_26811 : exactInterval 15 26811 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26811 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26811) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26811 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26811 : oddCount 26811 15 = 10 ∧ acceleratedOrbit 15 26811 = 48320 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26811 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26811) = 3 ^ 10 * m + 48320 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26811.1, data_15_26811.2]

/-- Complete interval computation for depth 15, residue 26812. -/
theorem bounds_15_26812 : exactInterval 15 26812 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26812 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26812) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26812 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26812 : oddCount 26812 15 = 9 ∧ acceleratedOrbit 15 26812 = 16109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26812 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26812) = 3 ^ 9 * m + 16109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26812.1, data_15_26812.2]

/-- Complete interval computation for depth 15, residue 26813. -/
theorem bounds_15_26813 : exactInterval 15 26813 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26813 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26813) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26813 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26813 : oddCount 26813 15 = 9 ∧ acceleratedOrbit 15 26813 = 16109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26813 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26813) = 3 ^ 9 * m + 16109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26813.1, data_15_26813.2]

/-- Complete interval computation for depth 15, residue 26814. -/
theorem bounds_15_26814 : exactInterval 15 26814 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26814 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26814) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26814 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26814 : oddCount 26814 15 = 9 ∧ acceleratedOrbit 15 26814 = 16109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26814 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26814) = 3 ^ 9 * m + 16109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26814.1, data_15_26814.2]

/-- Complete interval computation for depth 15, residue 26815. -/
theorem bounds_15_26815 : exactInterval 15 26815 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26815 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26815) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26815 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26815 : oddCount 26815 15 = 9 ∧ acceleratedOrbit 15 26815 = 16109 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26815 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26815) = 3 ^ 9 * m + 16109 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26815.1, data_15_26815.2]

/-- Complete interval computation for depth 15, residue 26816. -/
theorem bounds_15_26816 : exactInterval 15 26816 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26816 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26816) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26816 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26816 : oddCount 26816 15 = 4 ∧ acceleratedOrbit 15 26816 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26816 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26816) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26816.1, data_15_26816.2]

/-- Complete interval computation for depth 15, residue 26817. -/
theorem bounds_15_26817 : exactInterval 15 26817 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26817 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26817) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26817 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26817 : oddCount 26817 15 = 8 ∧ acceleratedOrbit 15 26817 = 5372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26817 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26817) = 3 ^ 8 * m + 5372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26817.1, data_15_26817.2]

/-- Complete interval computation for depth 15, residue 26818. -/
theorem bounds_15_26818 : exactInterval 15 26818 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26818 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26818) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26818 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26818 : oddCount 26818 15 = 8 ∧ acceleratedOrbit 15 26818 = 5372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26818 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26818) = 3 ^ 8 * m + 5372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26818.1, data_15_26818.2]

/-- Complete interval computation for depth 15, residue 26819. -/
theorem bounds_15_26819 : exactInterval 15 26819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26819 : oddCount 26819 15 = 8 ∧ acceleratedOrbit 15 26819 = 5372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26819) = 3 ^ 8 * m + 5372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26819.1, data_15_26819.2]

/-- Complete interval computation for depth 15, residue 26820. -/
theorem bounds_15_26820 : exactInterval 15 26820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26820 : oddCount 26820 15 = 7 ∧ acceleratedOrbit 15 26820 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26820) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26820.1, data_15_26820.2]

/-- Complete interval computation for depth 15, residue 26821. -/
theorem bounds_15_26821 : exactInterval 15 26821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26821 : oddCount 26821 15 = 7 ∧ acceleratedOrbit 15 26821 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26821) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26821.1, data_15_26821.2]

/-- Complete interval computation for depth 15, residue 26822. -/
theorem bounds_15_26822 : exactInterval 15 26822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26822 : oddCount 26822 15 = 7 ∧ acceleratedOrbit 15 26822 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26822) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26822.1, data_15_26822.2]

/-- Complete interval computation for depth 15, residue 26823. -/
theorem bounds_15_26823 : exactInterval 15 26823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26823 : oddCount 26823 15 = 9 ∧ acceleratedOrbit 15 26823 = 16114 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26823) = 3 ^ 9 * m + 16114 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26823.1, data_15_26823.2]

/-- Complete interval computation for depth 15, residue 26824. -/
theorem bounds_15_26824 : exactInterval 15 26824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26824 : oddCount 26824 15 = 7 ∧ acceleratedOrbit 15 26824 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26824) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26824.1, data_15_26824.2]

/-- Complete interval computation for depth 15, residue 26825. -/
theorem bounds_15_26825 : exactInterval 15 26825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26825 : oddCount 26825 15 = 5 ∧ acceleratedOrbit 15 26825 = 199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26825) = 3 ^ 5 * m + 199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26825.1, data_15_26825.2]

/-- Complete interval computation for depth 15, residue 26826. -/
theorem bounds_15_26826 : exactInterval 15 26826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26826 : oddCount 26826 15 = 7 ∧ acceleratedOrbit 15 26826 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26826) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26826.1, data_15_26826.2]

/-- Complete interval computation for depth 15, residue 26827. -/
theorem bounds_15_26827 : exactInterval 15 26827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26827 : oddCount 26827 15 = 10 ∧ acceleratedOrbit 15 26827 = 48356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26827) = 3 ^ 10 * m + 48356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26827.1, data_15_26827.2]

/-- Complete interval computation for depth 15, residue 26828. -/
theorem bounds_15_26828 : exactInterval 15 26828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26828 : oddCount 26828 15 = 7 ∧ acceleratedOrbit 15 26828 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26828) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26828.1, data_15_26828.2]

/-- Complete interval computation for depth 15, residue 26829. -/
theorem bounds_15_26829 : exactInterval 15 26829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26829 : oddCount 26829 15 = 7 ∧ acceleratedOrbit 15 26829 = 1792 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26829) = 3 ^ 7 * m + 1792 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26829.1, data_15_26829.2]

/-- Complete interval computation for depth 15, residue 26830. -/
theorem bounds_15_26830 : exactInterval 15 26830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26830 : oddCount 26830 15 = 11 ∧ acceleratedOrbit 15 26830 = 145061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26830) = 3 ^ 11 * m + 145061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26830.1, data_15_26830.2]

/-- Complete interval computation for depth 15, residue 26831. -/
theorem bounds_15_26831 : exactInterval 15 26831 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26831) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26831 : oddCount 26831 15 = 11 ∧ acceleratedOrbit 15 26831 = 145061 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26831) = 3 ^ 11 * m + 145061 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26831.1, data_15_26831.2]

/-- Complete interval computation for depth 15, residue 26832. -/
theorem bounds_15_26832 : exactInterval 15 26832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26832 : oddCount 26832 15 = 4 ∧ acceleratedOrbit 15 26832 = 67 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26832) = 3 ^ 4 * m + 67 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26832.1, data_15_26832.2]

/-- Complete interval computation for depth 15, residue 26833. -/
theorem bounds_15_26833 : exactInterval 15 26833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26833 : oddCount 26833 15 = 8 ∧ acceleratedOrbit 15 26833 = 5374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26833) = 3 ^ 8 * m + 5374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26833.1, data_15_26833.2]

/-- Complete interval computation for depth 15, residue 26834. -/
theorem bounds_15_26834 : exactInterval 15 26834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26834 : oddCount 26834 15 = 8 ∧ acceleratedOrbit 15 26834 = 5374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26834) = 3 ^ 8 * m + 5374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26834.1, data_15_26834.2]

/-- Complete interval computation for depth 15, residue 26835. -/
theorem bounds_15_26835 : exactInterval 15 26835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_26835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 26835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_26835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_26835 : oddCount 26835 15 = 8 ∧ acceleratedOrbit 15 26835 = 5374 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_26835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 26835) = 3 ^ 8 * m + 5374 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_26835.1, data_15_26835.2]

end Collatz.Research.PassageAtlas.Batch0819
