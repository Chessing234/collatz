import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0759

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 24838. -/
theorem bounds_15_24838 : exactInterval 15 24838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24838 : oddCount 24838 15 = 7 ∧ acceleratedOrbit 15 24838 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24838) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24838.1, data_15_24838.2]

/-- Complete interval computation for depth 15, residue 24839. -/
theorem bounds_15_24839 : exactInterval 15 24839 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24839) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24839 : oddCount 24839 15 = 11 ∧ acceleratedOrbit 15 24839 = 134297 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24839) = 3 ^ 11 * m + 134297 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24839.1, data_15_24839.2]

/-- Complete interval computation for depth 15, residue 24840. -/
theorem bounds_15_24840 : exactInterval 15 24840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24840 : oddCount 24840 15 = 7 ∧ acceleratedOrbit 15 24840 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24840) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24840.1, data_15_24840.2]

/-- Complete interval computation for depth 15, residue 24841. -/
theorem bounds_15_24841 : exactInterval 15 24841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24841 : oddCount 24841 15 = 9 ∧ acceleratedOrbit 15 24841 = 14924 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24841) = 3 ^ 9 * m + 14924 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24841.1, data_15_24841.2]

/-- Complete interval computation for depth 15, residue 24842. -/
theorem bounds_15_24842 : exactInterval 15 24842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24842 : oddCount 24842 15 = 7 ∧ acceleratedOrbit 15 24842 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24842) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24842.1, data_15_24842.2]

/-- Complete interval computation for depth 15, residue 24843. -/
theorem bounds_15_24843 : exactInterval 15 24843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24843 : oddCount 24843 15 = 6 ∧ acceleratedOrbit 15 24843 = 553 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24843) = 3 ^ 6 * m + 553 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24843.1, data_15_24843.2]

/-- Complete interval computation for depth 15, residue 24844. -/
theorem bounds_15_24844 : exactInterval 15 24844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24844 : oddCount 24844 15 = 7 ∧ acceleratedOrbit 15 24844 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24844) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24844.1, data_15_24844.2]

/-- Complete interval computation for depth 15, residue 24845. -/
theorem bounds_15_24845 : exactInterval 15 24845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24845 : oddCount 24845 15 = 7 ∧ acceleratedOrbit 15 24845 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24845) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24845.1, data_15_24845.2]

/-- Complete interval computation for depth 15, residue 24846. -/
theorem bounds_15_24846 : exactInterval 15 24846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24846 : oddCount 24846 15 = 9 ∧ acceleratedOrbit 15 24846 = 14930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24846) = 3 ^ 9 * m + 14930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24846.1, data_15_24846.2]

/-- Complete interval computation for depth 15, residue 24847. -/
theorem bounds_15_24847 : exactInterval 15 24847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24847 : oddCount 24847 15 = 9 ∧ acceleratedOrbit 15 24847 = 14930 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24847) = 3 ^ 9 * m + 14930 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24847.1, data_15_24847.2]

/-- Complete interval computation for depth 15, residue 24848. -/
theorem bounds_15_24848 : exactInterval 15 24848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24848 : oddCount 24848 15 = 4 ∧ acceleratedOrbit 15 24848 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24848) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24848.1, data_15_24848.2]

/-- Complete interval computation for depth 15, residue 24849. -/
theorem bounds_15_24849 : exactInterval 15 24849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24849 : oddCount 24849 15 = 7 ∧ acceleratedOrbit 15 24849 = 1660 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24849) = 3 ^ 7 * m + 1660 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24849.1, data_15_24849.2]

/-- Complete interval computation for depth 15, residue 24850. -/
theorem bounds_15_24850 : exactInterval 15 24850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24850 : oddCount 24850 15 = 10 ∧ acceleratedOrbit 15 24850 = 44788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24850) = 3 ^ 10 * m + 44788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24850.1, data_15_24850.2]

/-- Complete interval computation for depth 15, residue 24851. -/
theorem bounds_15_24851 : exactInterval 15 24851 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24851 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24851) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24851 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24851 : oddCount 24851 15 = 10 ∧ acceleratedOrbit 15 24851 = 44788 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24851 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24851) = 3 ^ 10 * m + 44788 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24851.1, data_15_24851.2]

/-- Complete interval computation for depth 15, residue 24852. -/
theorem bounds_15_24852 : exactInterval 15 24852 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24852 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24852) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24852 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24852 : oddCount 24852 15 = 4 ∧ acceleratedOrbit 15 24852 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24852 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24852) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24852.1, data_15_24852.2]

/-- Complete interval computation for depth 15, residue 24853. -/
theorem bounds_15_24853 : exactInterval 15 24853 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24853 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24853) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24853 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24853 : oddCount 24853 15 = 4 ∧ acceleratedOrbit 15 24853 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24853 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24853) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24853.1, data_15_24853.2]

/-- Complete interval computation for depth 15, residue 24854. -/
theorem bounds_15_24854 : exactInterval 15 24854 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24854 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24854) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24854 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24854 : oddCount 24854 15 = 8 ∧ acceleratedOrbit 15 24854 = 4978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24854 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24854) = 3 ^ 8 * m + 4978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24854.1, data_15_24854.2]

/-- Complete interval computation for depth 15, residue 24855. -/
theorem bounds_15_24855 : exactInterval 15 24855 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24855 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24855) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24855 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24855 : oddCount 24855 15 = 8 ∧ acceleratedOrbit 15 24855 = 4978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24855 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24855) = 3 ^ 8 * m + 4978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24855.1, data_15_24855.2]

/-- Complete interval computation for depth 15, residue 24856. -/
theorem bounds_15_24856 : exactInterval 15 24856 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24856 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24856) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24856 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24856 : oddCount 24856 15 = 4 ∧ acceleratedOrbit 15 24856 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24856 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24856) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24856.1, data_15_24856.2]

/-- Complete interval computation for depth 15, residue 24857. -/
theorem bounds_15_24857 : exactInterval 15 24857 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24857 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24857) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24857 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24857 : oddCount 24857 15 = 8 ∧ acceleratedOrbit 15 24857 = 4978 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24857 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24857) = 3 ^ 8 * m + 4978 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24857.1, data_15_24857.2]

/-- Complete interval computation for depth 15, residue 24858. -/
theorem bounds_15_24858 : exactInterval 15 24858 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24858 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24858) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24858 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24858 : oddCount 24858 15 = 4 ∧ acceleratedOrbit 15 24858 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24858 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24858) = 3 ^ 4 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24858.1, data_15_24858.2]

/-- Complete interval computation for depth 15, residue 24859. -/
theorem bounds_15_24859 : exactInterval 15 24859 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24859 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24859) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24859 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24859 : oddCount 24859 15 = 11 ∧ acceleratedOrbit 15 24859 = 134399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24859 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24859) = 3 ^ 11 * m + 134399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24859.1, data_15_24859.2]

/-- Complete interval computation for depth 15, residue 24860. -/
theorem bounds_15_24860 : exactInterval 15 24860 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24860 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24860) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24860 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24860 : oddCount 24860 15 = 8 ∧ acceleratedOrbit 15 24860 = 4979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24860 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24860) = 3 ^ 8 * m + 4979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24860.1, data_15_24860.2]

/-- Complete interval computation for depth 15, residue 24861. -/
theorem bounds_15_24861 : exactInterval 15 24861 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24861 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24861) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24861 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24861 : oddCount 24861 15 = 8 ∧ acceleratedOrbit 15 24861 = 4979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24861 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24861) = 3 ^ 8 * m + 4979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24861.1, data_15_24861.2]

/-- Complete interval computation for depth 15, residue 24862. -/
theorem bounds_15_24862 : exactInterval 15 24862 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24862 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24862) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24862 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24862 : oddCount 24862 15 = 8 ∧ acceleratedOrbit 15 24862 = 4979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24862 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24862) = 3 ^ 8 * m + 4979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24862.1, data_15_24862.2]

/-- Complete interval computation for depth 15, residue 24863. -/
theorem bounds_15_24863 : exactInterval 15 24863 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24863 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24863) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24863 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24863 : oddCount 24863 15 = 8 ∧ acceleratedOrbit 15 24863 = 4979 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24863 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24863) = 3 ^ 8 * m + 4979 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24863.1, data_15_24863.2]

/-- Complete interval computation for depth 15, residue 24864. -/
theorem bounds_15_24864 : exactInterval 15 24864 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24864 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24864) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24864 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24864 : oddCount 24864 15 = 7 ∧ acceleratedOrbit 15 24864 = 1664 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24864 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24864) = 3 ^ 7 * m + 1664 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24864.1, data_15_24864.2]

/-- Complete interval computation for depth 15, residue 24865. -/
theorem bounds_15_24865 : exactInterval 15 24865 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24865 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24865) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24865 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24865 : oddCount 24865 15 = 8 ∧ acceleratedOrbit 15 24865 = 4981 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24865 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24865) = 3 ^ 8 * m + 4981 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24865.1, data_15_24865.2]

/-- Complete interval computation for depth 15, residue 24866. -/
theorem bounds_15_24866 : exactInterval 15 24866 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24866 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24866) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24866 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24866 : oddCount 24866 15 = 9 ∧ acceleratedOrbit 15 24866 = 14944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24866 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24866) = 3 ^ 9 * m + 14944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24866.1, data_15_24866.2]

/-- Complete interval computation for depth 15, residue 24867. -/
theorem bounds_15_24867 : exactInterval 15 24867 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24867 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24867) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24867 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24867 : oddCount 24867 15 = 9 ∧ acceleratedOrbit 15 24867 = 14944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24867 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24867) = 3 ^ 9 * m + 14944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24867.1, data_15_24867.2]

/-- Complete interval computation for depth 15, residue 24868. -/
theorem bounds_15_24868 : exactInterval 15 24868 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24868 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24868) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24868 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24868 : oddCount 24868 15 = 9 ∧ acceleratedOrbit 15 24868 = 14944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24868 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24868) = 3 ^ 9 * m + 14944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24868.1, data_15_24868.2]

/-- Complete interval computation for depth 15, residue 24869. -/
theorem bounds_15_24869 : exactInterval 15 24869 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_24869 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 24869) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_24869 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_24869 : oddCount 24869 15 = 9 ∧ acceleratedOrbit 15 24869 = 14944 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_24869 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 24869) = 3 ^ 9 * m + 14944 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_24869.1, data_15_24869.2]

end Collatz.Research.PassageAtlas.Batch0759
