import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0026

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 819. -/
theorem bounds_15_819 : exactInterval 15 819 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_819 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 819) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_819 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_819 : oddCount 819 15 = 7 ∧ acceleratedOrbit 15 819 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_819 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 819) = 3 ^ 7 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_819.1, data_15_819.2]

/-- Complete interval computation for depth 15, residue 820. -/
theorem bounds_15_820 : exactInterval 15 820 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_820 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 820) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_820 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_820 : oddCount 820 15 = 6 ∧ acceleratedOrbit 15 820 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_820 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 820) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_820.1, data_15_820.2]

/-- Complete interval computation for depth 15, residue 821. -/
theorem bounds_15_821 : exactInterval 15 821 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_821 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 821) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_821 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_821 : oddCount 821 15 = 6 ∧ acceleratedOrbit 15 821 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_821 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 821) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_821.1, data_15_821.2]

/-- Complete interval computation for depth 15, residue 822. -/
theorem bounds_15_822 : exactInterval 15 822 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_822 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 822) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_822 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_822 : oddCount 822 15 = 9 ∧ acceleratedOrbit 15 822 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_822 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 822) = 3 ^ 9 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_822.1, data_15_822.2]

/-- Complete interval computation for depth 15, residue 823. -/
theorem bounds_15_823 : exactInterval 15 823 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_823 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 823) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_823 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_823 : oddCount 823 15 = 9 ∧ acceleratedOrbit 15 823 = 496 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_823 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 823) = 3 ^ 9 * m + 496 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_823.1, data_15_823.2]

/-- Complete interval computation for depth 15, residue 824. -/
theorem bounds_15_824 : exactInterval 15 824 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_824 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 824) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_824 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_824 : oddCount 824 15 = 8 ∧ acceleratedOrbit 15 824 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_824 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 824) = 3 ^ 8 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_824.1, data_15_824.2]

/-- Complete interval computation for depth 15, residue 825. -/
theorem bounds_15_825 : exactInterval 15 825 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_825 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 825) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_825 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_825 : oddCount 825 15 = 8 ∧ acceleratedOrbit 15 825 = 166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_825 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 825) = 3 ^ 8 * m + 166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_825.1, data_15_825.2]

/-- Complete interval computation for depth 15, residue 826. -/
theorem bounds_15_826 : exactInterval 15 826 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_826 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 826) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_826 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_826 : oddCount 826 15 = 8 ∧ acceleratedOrbit 15 826 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_826 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 826) = 3 ^ 8 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_826.1, data_15_826.2]

/-- Complete interval computation for depth 15, residue 827. -/
theorem bounds_15_827 : exactInterval 15 827 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_827 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 827) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_827 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_827 : oddCount 827 15 = 7 ∧ acceleratedOrbit 15 827 = 56 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_827 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 827) = 3 ^ 7 * m + 56 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_827.1, data_15_827.2]

/-- Complete interval computation for depth 15, residue 828. -/
theorem bounds_15_828 : exactInterval 15 828 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_828 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 828) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_828 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_828 : oddCount 828 15 = 8 ∧ acceleratedOrbit 15 828 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_828 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 828) = 3 ^ 8 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_828.1, data_15_828.2]

/-- Complete interval computation for depth 15, residue 829. -/
theorem bounds_15_829 : exactInterval 15 829 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_829 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 829) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_829 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_829 : oddCount 829 15 = 8 ∧ acceleratedOrbit 15 829 = 167 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_829 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 829) = 3 ^ 8 * m + 167 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_829.1, data_15_829.2]

/-- Complete interval computation for depth 15, residue 830. -/
theorem bounds_15_830 : exactInterval 15 830 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_830 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 830) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_830 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_830 : oddCount 830 15 = 9 ∧ acceleratedOrbit 15 830 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_830 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 830) = 3 ^ 9 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_830.1, data_15_830.2]

/-- Complete interval computation for depth 15, residue 831. -/
theorem bounds_15_831 : exactInterval 15 831 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_831 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 831) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_831 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_831 : oddCount 831 15 = 9 ∧ acceleratedOrbit 15 831 = 500 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_831 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 831) = 3 ^ 9 * m + 500 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_831.1, data_15_831.2]

/-- Complete interval computation for depth 15, residue 832. -/
theorem bounds_15_832 : exactInterval 15 832 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_832 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 832) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_832 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_832 : oddCount 832 15 = 3 ∧ acceleratedOrbit 15 832 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_832 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 832) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_832.1, data_15_832.2]

/-- Complete interval computation for depth 15, residue 833. -/
theorem bounds_15_833 : exactInterval 15 833 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_833 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 833) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_833 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_833 : oddCount 833 15 = 6 ∧ acceleratedOrbit 15 833 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_833 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 833) = 3 ^ 6 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_833.1, data_15_833.2]

/-- Complete interval computation for depth 15, residue 834. -/
theorem bounds_15_834 : exactInterval 15 834 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_834 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 834) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_834 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_834 : oddCount 834 15 = 9 ∧ acceleratedOrbit 15 834 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_834 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 834) = 3 ^ 9 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_834.1, data_15_834.2]

/-- Complete interval computation for depth 15, residue 835. -/
theorem bounds_15_835 : exactInterval 15 835 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_835 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 835) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_835 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_835 : oddCount 835 15 = 9 ∧ acceleratedOrbit 15 835 = 506 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_835 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 835) = 3 ^ 9 * m + 506 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_835.1, data_15_835.2]

/-- Complete interval computation for depth 15, residue 836. -/
theorem bounds_15_836 : exactInterval 15 836 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_836 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 836) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_836 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_836 : oddCount 836 15 = 6 ∧ acceleratedOrbit 15 836 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_836 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 836) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_836.1, data_15_836.2]

/-- Complete interval computation for depth 15, residue 837. -/
theorem bounds_15_837 : exactInterval 15 837 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_837 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 837) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_837 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_837 : oddCount 837 15 = 6 ∧ acceleratedOrbit 15 837 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_837 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 837) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_837.1, data_15_837.2]

/-- Complete interval computation for depth 15, residue 838. -/
theorem bounds_15_838 : exactInterval 15 838 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_838 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 838) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_838 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_838 : oddCount 838 15 = 6 ∧ acceleratedOrbit 15 838 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_838 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 838) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_838.1, data_15_838.2]

/-- Complete interval computation for depth 15, residue 839. -/
theorem bounds_15_839 : exactInterval 15 839 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_839 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 839) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_839 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_839 : oddCount 839 15 = 9 ∧ acceleratedOrbit 15 839 = 505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_839 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 839) = 3 ^ 9 * m + 505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_839.1, data_15_839.2]

/-- Complete interval computation for depth 15, residue 840. -/
theorem bounds_15_840 : exactInterval 15 840 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_840 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 840) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_840 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_840 : oddCount 840 15 = 6 ∧ acceleratedOrbit 15 840 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_840 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 840) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_840.1, data_15_840.2]

/-- Complete interval computation for depth 15, residue 841. -/
theorem bounds_15_841 : exactInterval 15 841 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_841 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 841) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_841 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_841 : oddCount 841 15 = 6 ∧ acceleratedOrbit 15 841 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_841 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 841) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_841.1, data_15_841.2]

/-- Complete interval computation for depth 15, residue 842. -/
theorem bounds_15_842 : exactInterval 15 842 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_842 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 842) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_842 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_842 : oddCount 842 15 = 6 ∧ acceleratedOrbit 15 842 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_842 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 842) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_842.1, data_15_842.2]

/-- Complete interval computation for depth 15, residue 843. -/
theorem bounds_15_843 : exactInterval 15 843 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_843 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 843) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_843 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_843 : oddCount 843 15 = 6 ∧ acceleratedOrbit 15 843 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_843 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 843) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_843.1, data_15_843.2]

/-- Complete interval computation for depth 15, residue 844. -/
theorem bounds_15_844 : exactInterval 15 844 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_844 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 844) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_844 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_844 : oddCount 844 15 = 6 ∧ acceleratedOrbit 15 844 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_844 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 844) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_844.1, data_15_844.2]

/-- Complete interval computation for depth 15, residue 845. -/
theorem bounds_15_845 : exactInterval 15 845 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_845 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 845) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_845 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_845 : oddCount 845 15 = 6 ∧ acceleratedOrbit 15 845 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_845 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 845) = 3 ^ 6 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_845.1, data_15_845.2]

/-- Complete interval computation for depth 15, residue 846. -/
theorem bounds_15_846 : exactInterval 15 846 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_846 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 846) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_846 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_846 : oddCount 846 15 = 9 ∧ acceleratedOrbit 15 846 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_846 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 846) = 3 ^ 9 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_846.1, data_15_846.2]

/-- Complete interval computation for depth 15, residue 847. -/
theorem bounds_15_847 : exactInterval 15 847 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_847 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 847) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_847 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_847 : oddCount 847 15 = 9 ∧ acceleratedOrbit 15 847 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_847 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 847) = 3 ^ 9 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_847.1, data_15_847.2]

/-- Complete interval computation for depth 15, residue 848. -/
theorem bounds_15_848 : exactInterval 15 848 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_848 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 848) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_848 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_848 : oddCount 848 15 = 3 ∧ acceleratedOrbit 15 848 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_848 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 848) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_848.1, data_15_848.2]

/-- Complete interval computation for depth 15, residue 849. -/
theorem bounds_15_849 : exactInterval 15 849 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_849 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 849) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_849 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_849 : oddCount 849 15 = 11 ∧ acceleratedOrbit 15 849 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_849 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 849) = 3 ^ 11 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_849.1, data_15_849.2]

/-- Complete interval computation for depth 15, residue 850. -/
theorem bounds_15_850 : exactInterval 15 850 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_850 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 850) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_850 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_850 : oddCount 850 15 = 11 ∧ acceleratedOrbit 15 850 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_850 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 850) = 3 ^ 11 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_850.1, data_15_850.2]

end Collatz.Research.PassageAtlas.Batch0026
