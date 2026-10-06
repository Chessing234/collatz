import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0852

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 27885. -/
theorem bounds_15_27885 : exactInterval 15 27885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27885 : oddCount 27885 15 = 8 ∧ acceleratedOrbit 15 27885 = 5588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27885) = 3 ^ 8 * m + 5588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27885.1, data_15_27885.2]

/-- Complete interval computation for depth 15, residue 27886. -/
theorem bounds_15_27886 : exactInterval 15 27886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27886 : oddCount 27886 15 = 8 ∧ acceleratedOrbit 15 27886 = 5588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27886) = 3 ^ 8 * m + 5588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27886.1, data_15_27886.2]

/-- Complete interval computation for depth 15, residue 27887. -/
theorem bounds_15_27887 : exactInterval 15 27887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27887 : oddCount 27887 15 = 12 ∧ acceleratedOrbit 15 27887 = 452299 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27887) = 3 ^ 12 * m + 452299 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27887.1, data_15_27887.2]

/-- Complete interval computation for depth 15, residue 27888. -/
theorem bounds_15_27888 : exactInterval 15 27888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27888 : oddCount 27888 15 = 9 ∧ acceleratedOrbit 15 27888 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27888) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27888.1, data_15_27888.2]

/-- Complete interval computation for depth 15, residue 27889. -/
theorem bounds_15_27889 : exactInterval 15 27889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27889 : oddCount 27889 15 = 9 ∧ acceleratedOrbit 15 27889 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27889) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27889.1, data_15_27889.2]

/-- Complete interval computation for depth 15, residue 27890. -/
theorem bounds_15_27890 : exactInterval 15 27890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27890 : oddCount 27890 15 = 9 ∧ acceleratedOrbit 15 27890 = 16757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27890) = 3 ^ 9 * m + 16757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27890.1, data_15_27890.2]

/-- Complete interval computation for depth 15, residue 27891. -/
theorem bounds_15_27891 : exactInterval 15 27891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27891 : oddCount 27891 15 = 9 ∧ acceleratedOrbit 15 27891 = 16757 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27891) = 3 ^ 9 * m + 16757 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27891.1, data_15_27891.2]

/-- Complete interval computation for depth 15, residue 27892. -/
theorem bounds_15_27892 : exactInterval 15 27892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27892 : oddCount 27892 15 = 9 ∧ acceleratedOrbit 15 27892 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27892) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27892.1, data_15_27892.2]

/-- Complete interval computation for depth 15, residue 27893. -/
theorem bounds_15_27893 : exactInterval 15 27893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27893 : oddCount 27893 15 = 9 ∧ acceleratedOrbit 15 27893 = 16766 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27893) = 3 ^ 9 * m + 16766 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27893.1, data_15_27893.2]

/-- Complete interval computation for depth 15, residue 27894. -/
theorem bounds_15_27894 : exactInterval 15 27894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27894 : oddCount 27894 15 = 8 ∧ acceleratedOrbit 15 27894 = 5588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27894) = 3 ^ 8 * m + 5588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27894.1, data_15_27894.2]

/-- Complete interval computation for depth 15, residue 27895. -/
theorem bounds_15_27895 : exactInterval 15 27895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27895 : oddCount 27895 15 = 8 ∧ acceleratedOrbit 15 27895 = 5588 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27895) = 3 ^ 8 * m + 5588 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27895.1, data_15_27895.2]

/-- Complete interval computation for depth 15, residue 27896. -/
theorem bounds_15_27896 : exactInterval 15 27896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27896 : oddCount 27896 15 = 9 ∧ acceleratedOrbit 15 27896 = 16762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27896) = 3 ^ 9 * m + 16762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27896.1, data_15_27896.2]

/-- Complete interval computation for depth 15, residue 27897. -/
theorem bounds_15_27897 : exactInterval 15 27897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27897 : oddCount 27897 15 = 9 ∧ acceleratedOrbit 15 27897 = 16760 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27897) = 3 ^ 9 * m + 16760 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27897.1, data_15_27897.2]

/-- Complete interval computation for depth 15, residue 27898. -/
theorem bounds_15_27898 : exactInterval 15 27898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27898 : oddCount 27898 15 = 9 ∧ acceleratedOrbit 15 27898 = 16762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27898) = 3 ^ 9 * m + 16762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27898.1, data_15_27898.2]

/-- Complete interval computation for depth 15, residue 27899. -/
theorem bounds_15_27899 : exactInterval 15 27899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27899 : oddCount 27899 15 = 11 ∧ acceleratedOrbit 15 27899 = 150835 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27899) = 3 ^ 11 * m + 150835 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27899.1, data_15_27899.2]

/-- Complete interval computation for depth 15, residue 27900. -/
theorem bounds_15_27900 : exactInterval 15 27900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27900 : oddCount 27900 15 = 9 ∧ acceleratedOrbit 15 27900 = 16762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27900) = 3 ^ 9 * m + 16762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27900.1, data_15_27900.2]

/-- Complete interval computation for depth 15, residue 27901. -/
theorem bounds_15_27901 : exactInterval 15 27901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27901 : oddCount 27901 15 = 9 ∧ acceleratedOrbit 15 27901 = 16762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27901) = 3 ^ 9 * m + 16762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27901.1, data_15_27901.2]

/-- Complete interval computation for depth 15, residue 27902. -/
theorem bounds_15_27902 : exactInterval 15 27902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27902 : oddCount 27902 15 = 10 ∧ acceleratedOrbit 15 27902 = 50284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27902) = 3 ^ 10 * m + 50284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27902.1, data_15_27902.2]

/-- Complete interval computation for depth 15, residue 27903. -/
theorem bounds_15_27903 : exactInterval 15 27903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27903 : oddCount 27903 15 = 10 ∧ acceleratedOrbit 15 27903 = 50284 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27903) = 3 ^ 10 * m + 50284 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27903.1, data_15_27903.2]

/-- Complete interval computation for depth 15, residue 27904. -/
theorem bounds_15_27904 : exactInterval 15 27904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27904 : oddCount 27904 15 = 4 ∧ acceleratedOrbit 15 27904 = 71 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27904) = 3 ^ 4 * m + 71 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27904.1, data_15_27904.2]

/-- Complete interval computation for depth 15, residue 27905. -/
theorem bounds_15_27905 : exactInterval 15 27905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27905 : oddCount 27905 15 = 10 ∧ acceleratedOrbit 15 27905 = 50300 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27905) = 3 ^ 10 * m + 50300 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27905.1, data_15_27905.2]

/-- Complete interval computation for depth 15, residue 27906. -/
theorem bounds_15_27906 : exactInterval 15 27906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27906 : oddCount 27906 15 = 11 ∧ acceleratedOrbit 15 27906 = 150902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27906) = 3 ^ 11 * m + 150902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27906.1, data_15_27906.2]

/-- Complete interval computation for depth 15, residue 27907. -/
theorem bounds_15_27907 : exactInterval 15 27907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27907 : oddCount 27907 15 = 11 ∧ acceleratedOrbit 15 27907 = 150902 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27907) = 3 ^ 11 * m + 150902 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27907.1, data_15_27907.2]

/-- Complete interval computation for depth 15, residue 27908. -/
theorem bounds_15_27908 : exactInterval 15 27908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27908 : oddCount 27908 15 = 3 ∧ acceleratedOrbit 15 27908 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27908) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27908.1, data_15_27908.2]

/-- Complete interval computation for depth 15, residue 27909. -/
theorem bounds_15_27909 : exactInterval 15 27909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27909 : oddCount 27909 15 = 3 ∧ acceleratedOrbit 15 27909 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27909) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27909.1, data_15_27909.2]

/-- Complete interval computation for depth 15, residue 27910. -/
theorem bounds_15_27910 : exactInterval 15 27910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27910 : oddCount 27910 15 = 3 ∧ acceleratedOrbit 15 27910 = 23 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27910) = 3 ^ 3 * m + 23 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27910.1, data_15_27910.2]

/-- Complete interval computation for depth 15, residue 27911. -/
theorem bounds_15_27911 : exactInterval 15 27911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27911 : oddCount 27911 15 = 12 ∧ acceleratedOrbit 15 27911 = 452708 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27911) = 3 ^ 12 * m + 452708 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27911.1, data_15_27911.2]

/-- Complete interval computation for depth 15, residue 27912. -/
theorem bounds_15_27912 : exactInterval 15 27912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27912 : oddCount 27912 15 = 7 ∧ acceleratedOrbit 15 27912 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27912) = 3 ^ 7 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27912.1, data_15_27912.2]

/-- Complete interval computation for depth 15, residue 27913. -/
theorem bounds_15_27913 : exactInterval 15 27913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27913 : oddCount 27913 15 = 9 ∧ acceleratedOrbit 15 27913 = 16769 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27913) = 3 ^ 9 * m + 16769 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27913.1, data_15_27913.2]

/-- Complete interval computation for depth 15, residue 27914. -/
theorem bounds_15_27914 : exactInterval 15 27914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27914 : oddCount 27914 15 = 7 ∧ acceleratedOrbit 15 27914 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27914) = 3 ^ 7 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27914.1, data_15_27914.2]

/-- Complete interval computation for depth 15, residue 27915. -/
theorem bounds_15_27915 : exactInterval 15 27915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27915 : oddCount 27915 15 = 8 ∧ acceleratedOrbit 15 27915 = 5591 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27915) = 3 ^ 8 * m + 5591 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27915.1, data_15_27915.2]

/-- Complete interval computation for depth 15, residue 27916. -/
theorem bounds_15_27916 : exactInterval 15 27916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27916 : oddCount 27916 15 = 7 ∧ acceleratedOrbit 15 27916 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27916) = 3 ^ 7 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27916.1, data_15_27916.2]

/-- Complete interval computation for depth 15, residue 27917. -/
theorem bounds_15_27917 : exactInterval 15 27917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_27917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 27917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_27917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_27917 : oddCount 27917 15 = 7 ∧ acceleratedOrbit 15 27917 = 1865 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_27917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 27917) = 3 ^ 7 * m + 1865 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_27917.1, data_15_27917.2]

end Collatz.Research.PassageAtlas.Batch0852
