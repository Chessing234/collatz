import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0942

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 30834. -/
theorem bounds_15_30834 : exactInterval 15 30834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30834 : oddCount 30834 15 = 8 ∧ acceleratedOrbit 15 30834 = 6176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30834) = 3 ^ 8 * m + 6176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30834.1, data_15_30834.2]

/-- Complete interval computation for depth 15, residue 30835. -/
theorem bounds_15_30835 : exactInterval 15 30835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30835 : oddCount 30835 15 = 8 ∧ acceleratedOrbit 15 30835 = 6176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30835) = 3 ^ 8 * m + 6176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30835.1, data_15_30835.2]

/-- Complete interval computation for depth 15, residue 30836. -/
theorem bounds_15_30836 : exactInterval 15 30836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30836 : oddCount 30836 15 = 5 ∧ acceleratedOrbit 15 30836 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30836) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30836.1, data_15_30836.2]

/-- Complete interval computation for depth 15, residue 30837. -/
theorem bounds_15_30837 : exactInterval 15 30837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30837 : oddCount 30837 15 = 5 ∧ acceleratedOrbit 15 30837 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30837) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30837.1, data_15_30837.2]

/-- Complete interval computation for depth 15, residue 30838. -/
theorem bounds_15_30838 : exactInterval 15 30838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30838 : oddCount 30838 15 = 8 ∧ acceleratedOrbit 15 30838 = 6176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30838) = 3 ^ 8 * m + 6176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30838.1, data_15_30838.2]

/-- Complete interval computation for depth 15, residue 30839. -/
theorem bounds_15_30839 : exactInterval 15 30839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30839 : oddCount 30839 15 = 8 ∧ acceleratedOrbit 15 30839 = 6176 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30839) = 3 ^ 8 * m + 6176 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30839.1, data_15_30839.2]

/-- Complete interval computation for depth 15, residue 30840. -/
theorem bounds_15_30840 : exactInterval 15 30840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30840 : oddCount 30840 15 = 5 ∧ acceleratedOrbit 15 30840 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30840) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30840.1, data_15_30840.2]

/-- Complete interval computation for depth 15, residue 30841. -/
theorem bounds_15_30841 : exactInterval 15 30841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30841 : oddCount 30841 15 = 9 ∧ acceleratedOrbit 15 30841 = 18527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30841) = 3 ^ 9 * m + 18527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30841.1, data_15_30841.2]

/-- Complete interval computation for depth 15, residue 30842. -/
theorem bounds_15_30842 : exactInterval 15 30842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30842 : oddCount 30842 15 = 5 ∧ acceleratedOrbit 15 30842 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30842) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30842.1, data_15_30842.2]

/-- Complete interval computation for depth 15, residue 30843. -/
theorem bounds_15_30843 : exactInterval 15 30843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30843 : oddCount 30843 15 = 10 ∧ acceleratedOrbit 15 30843 = 55586 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30843) = 3 ^ 10 * m + 55586 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30843.1, data_15_30843.2]

/-- Complete interval computation for depth 15, residue 30844. -/
theorem bounds_15_30844 : exactInterval 15 30844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30844 : oddCount 30844 15 = 10 ∧ acceleratedOrbit 15 30844 = 55592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30844) = 3 ^ 10 * m + 55592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30844.1, data_15_30844.2]

/-- Complete interval computation for depth 15, residue 30845. -/
theorem bounds_15_30845 : exactInterval 15 30845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30845 : oddCount 30845 15 = 10 ∧ acceleratedOrbit 15 30845 = 55592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30845) = 3 ^ 10 * m + 55592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30845.1, data_15_30845.2]

/-- Complete interval computation for depth 15, residue 30846. -/
theorem bounds_15_30846 : exactInterval 15 30846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30846 : oddCount 30846 15 = 10 ∧ acceleratedOrbit 15 30846 = 55592 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30846) = 3 ^ 10 * m + 55592 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30846.1, data_15_30846.2]

/-- Complete interval computation for depth 15, residue 30847. -/
theorem bounds_15_30847 : exactInterval 15 30847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30847 : oddCount 30847 15 = 11 ∧ acceleratedOrbit 15 30847 = 166769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30847) = 3 ^ 11 * m + 166769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30847.1, data_15_30847.2]

/-- Complete interval computation for depth 15, residue 30848. -/
theorem bounds_15_30848 : exactInterval 15 30848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30848 : oddCount 30848 15 = 3 ∧ acceleratedOrbit 15 30848 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30848) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30848.1, data_15_30848.2]

/-- Complete interval computation for depth 15, residue 30849. -/
theorem bounds_15_30849 : exactInterval 15 30849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30849 : oddCount 30849 15 = 8 ∧ acceleratedOrbit 15 30849 = 6178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30849) = 3 ^ 8 * m + 6178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30849.1, data_15_30849.2]

/-- Complete interval computation for depth 15, residue 30850. -/
theorem bounds_15_30850 : exactInterval 15 30850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30850 : oddCount 30850 15 = 8 ∧ acceleratedOrbit 15 30850 = 6182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30850) = 3 ^ 8 * m + 6182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30850.1, data_15_30850.2]

/-- Complete interval computation for depth 15, residue 30851. -/
theorem bounds_15_30851 : exactInterval 15 30851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30851 : oddCount 30851 15 = 8 ∧ acceleratedOrbit 15 30851 = 6182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30851) = 3 ^ 8 * m + 6182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30851.1, data_15_30851.2]

/-- Complete interval computation for depth 15, residue 30852. -/
theorem bounds_15_30852 : exactInterval 15 30852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30852 : oddCount 30852 15 = 8 ∧ acceleratedOrbit 15 30852 = 6182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30852) = 3 ^ 8 * m + 6182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30852.1, data_15_30852.2]

/-- Complete interval computation for depth 15, residue 30853. -/
theorem bounds_15_30853 : exactInterval 15 30853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30853 : oddCount 30853 15 = 8 ∧ acceleratedOrbit 15 30853 = 6182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30853) = 3 ^ 8 * m + 6182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30853.1, data_15_30853.2]

/-- Complete interval computation for depth 15, residue 30854. -/
theorem bounds_15_30854 : exactInterval 15 30854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30854 : oddCount 30854 15 = 8 ∧ acceleratedOrbit 15 30854 = 6182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30854) = 3 ^ 8 * m + 6182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30854.1, data_15_30854.2]

/-- Complete interval computation for depth 15, residue 30855. -/
theorem bounds_15_30855 : exactInterval 15 30855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30855 : oddCount 30855 15 = 7 ∧ acceleratedOrbit 15 30855 = 2060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30855) = 3 ^ 7 * m + 2060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30855.1, data_15_30855.2]

/-- Complete interval computation for depth 15, residue 30856. -/
theorem bounds_15_30856 : exactInterval 15 30856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30856 : oddCount 30856 15 = 6 ∧ acceleratedOrbit 15 30856 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30856) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30856.1, data_15_30856.2]

/-- Complete interval computation for depth 15, residue 30857. -/
theorem bounds_15_30857 : exactInterval 15 30857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30857 : oddCount 30857 15 = 10 ∧ acceleratedOrbit 15 30857 = 55610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30857) = 3 ^ 10 * m + 55610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30857.1, data_15_30857.2]

/-- Complete interval computation for depth 15, residue 30858. -/
theorem bounds_15_30858 : exactInterval 15 30858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30858 : oddCount 30858 15 = 6 ∧ acceleratedOrbit 15 30858 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30858) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30858.1, data_15_30858.2]

/-- Complete interval computation for depth 15, residue 30859. -/
theorem bounds_15_30859 : exactInterval 15 30859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30859 : oddCount 30859 15 = 9 ∧ acceleratedOrbit 15 30859 = 18539 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30859) = 3 ^ 9 * m + 18539 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30859.1, data_15_30859.2]

/-- Complete interval computation for depth 15, residue 30860. -/
theorem bounds_15_30860 : exactInterval 15 30860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30860 : oddCount 30860 15 = 6 ∧ acceleratedOrbit 15 30860 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30860) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30860.1, data_15_30860.2]

/-- Complete interval computation for depth 15, residue 30861. -/
theorem bounds_15_30861 : exactInterval 15 30861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30861 : oddCount 30861 15 = 6 ∧ acceleratedOrbit 15 30861 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30861) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30861.1, data_15_30861.2]

/-- Complete interval computation for depth 15, residue 30862. -/
theorem bounds_15_30862 : exactInterval 15 30862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30862 : oddCount 30862 15 = 7 ∧ acceleratedOrbit 15 30862 = 2060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30862) = 3 ^ 7 * m + 2060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30862.1, data_15_30862.2]

/-- Complete interval computation for depth 15, residue 30863. -/
theorem bounds_15_30863 : exactInterval 15 30863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30863 : oddCount 30863 15 = 7 ∧ acceleratedOrbit 15 30863 = 2060 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30863) = 3 ^ 7 * m + 2060 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30863.1, data_15_30863.2]

/-- Complete interval computation for depth 15, residue 30864. -/
theorem bounds_15_30864 : exactInterval 15 30864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30864 : oddCount 30864 15 = 7 ∧ acceleratedOrbit 15 30864 = 2062 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30864) = 3 ^ 7 * m + 2062 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30864.1, data_15_30864.2]

/-- Complete interval computation for depth 15, residue 30865. -/
theorem bounds_15_30865 : exactInterval 15 30865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30865 : oddCount 30865 15 = 9 ∧ acceleratedOrbit 15 30865 = 18544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30865) = 3 ^ 9 * m + 18544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30865.1, data_15_30865.2]

/-- Complete interval computation for depth 15, residue 30866. -/
theorem bounds_15_30866 : exactInterval 15 30866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_30866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 30866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_30866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_30866 : oddCount 30866 15 = 9 ∧ acceleratedOrbit 15 30866 = 18544 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_30866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 30866) = 3 ^ 9 * m + 18544 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_30866.1, data_15_30866.2]

end Collatz.Research.PassageAtlas.Batch0942
