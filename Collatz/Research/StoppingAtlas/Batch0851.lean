import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0851

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 5888. -/
theorem bounds_13_5888 : exactInterval 13 5888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5888 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5888) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5888 : oddCount 5888 13 = 3 ∧ acceleratedOrbit 13 5888 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5888 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5888) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5888.1, data_13_5888.2]

/-- Complete interval computation for depth 13, residue 5889. -/
theorem bounds_13_5889 : exactInterval 13 5889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5889 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5889) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5889 : oddCount 5889 13 = 5 ∧ acceleratedOrbit 13 5889 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5889 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5889) = 3 ^ 5 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5889.1, data_13_5889.2]

/-- Complete interval computation for depth 13, residue 5890. -/
theorem bounds_13_5890 : exactInterval 13 5890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5890 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5890) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5890 : oddCount 5890 13 = 8 ∧ acceleratedOrbit 13 5890 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5890 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5890) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5890.1, data_13_5890.2]

/-- Complete interval computation for depth 13, residue 5891. -/
theorem bounds_13_5891 : exactInterval 13 5891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5891 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5891) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5891 : oddCount 5891 13 = 8 ∧ acceleratedOrbit 13 5891 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5891 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5891) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5891.1, data_13_5891.2]

/-- Complete interval computation for depth 13, residue 5892. -/
theorem bounds_13_5892 : exactInterval 13 5892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5892 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5892) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5892 : oddCount 5892 13 = 6 ∧ acceleratedOrbit 13 5892 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5892 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5892) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5892.1, data_13_5892.2]

/-- Complete interval computation for depth 13, residue 5893. -/
theorem bounds_13_5893 : exactInterval 13 5893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5893 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5893) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5893 : oddCount 5893 13 = 6 ∧ acceleratedOrbit 13 5893 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5893 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5893) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5893.1, data_13_5893.2]

/-- Complete interval computation for depth 13, residue 5894. -/
theorem bounds_13_5894 : exactInterval 13 5894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5894 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5894) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5894 : oddCount 5894 13 = 6 ∧ acceleratedOrbit 13 5894 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5894 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5894) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5894.1, data_13_5894.2]

/-- Complete interval computation for depth 13, residue 5895. -/
theorem bounds_13_5895 : exactInterval 13 5895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5895 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5895) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5895 : oddCount 5895 13 = 8 ∧ acceleratedOrbit 13 5895 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5895 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5895) = 3 ^ 8 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5895.1, data_13_5895.2]

/-- Complete interval computation for depth 13, residue 5896. -/
theorem bounds_13_5896 : exactInterval 13 5896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5896 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5896) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5896 : oddCount 5896 13 = 7 ∧ acceleratedOrbit 13 5896 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5896 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5896) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5896.1, data_13_5896.2]

/-- Complete interval computation for depth 13, residue 5897. -/
theorem bounds_13_5897 : exactInterval 13 5897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5897 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5897) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5897 : oddCount 5897 13 = 10 ∧ acceleratedOrbit 13 5897 = 42524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5897 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5897) = 3 ^ 10 * m + 42524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5897.1, data_13_5897.2]

/-- Complete interval computation for depth 13, residue 5898. -/
theorem bounds_13_5898 : exactInterval 13 5898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5898 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5898) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5898 : oddCount 5898 13 = 7 ∧ acceleratedOrbit 13 5898 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5898 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5898) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5898.1, data_13_5898.2]

/-- Complete interval computation for depth 13, residue 5899. -/
theorem bounds_13_5899 : exactInterval 13 5899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5899 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5899) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5899 : oddCount 5899 13 = 7 ∧ acceleratedOrbit 13 5899 = 1576 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5899 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5899) = 3 ^ 7 * m + 1576 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5899.1, data_13_5899.2]

/-- Complete interval computation for depth 13, residue 5900. -/
theorem bounds_13_5900 : exactInterval 13 5900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5900 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5900) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5900 : oddCount 5900 13 = 7 ∧ acceleratedOrbit 13 5900 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5900 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5900) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5900.1, data_13_5900.2]

/-- Complete interval computation for depth 13, residue 5901. -/
theorem bounds_13_5901 : exactInterval 13 5901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5901 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5901) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5901 : oddCount 5901 13 = 7 ∧ acceleratedOrbit 13 5901 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5901 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5901) = 3 ^ 7 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5901.1, data_13_5901.2]

/-- Complete interval computation for depth 13, residue 5902. -/
theorem bounds_13_5902 : exactInterval 13 5902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_5902 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 5902) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_5902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_5902 : oddCount 5902 13 = 6 ∧ acceleratedOrbit 13 5902 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_5902 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 5902) = 3 ^ 6 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_5902.1, data_13_5902.2]

end Collatz.Research.StoppingAtlas.Batch0851
