import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0787

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 4904. -/
theorem bounds_13_4904 : exactInterval 13 4904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4904 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4904) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4904 : oddCount 4904 13 = 4 ∧ acceleratedOrbit 13 4904 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4904 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4904) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4904.1, data_13_4904.2]

/-- Complete interval computation for depth 13, residue 4905. -/
theorem bounds_13_4905 : exactInterval 13 4905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4905 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4905) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4905 : oddCount 4905 13 = 7 ∧ acceleratedOrbit 13 4905 = 1310 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4905 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4905) = 3 ^ 7 * m + 1310 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4905.1, data_13_4905.2]

/-- Complete interval computation for depth 13, residue 4906. -/
theorem bounds_13_4906 : exactInterval 13 4906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4906 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4906) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4906 : oddCount 4906 13 = 4 ∧ acceleratedOrbit 13 4906 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4906 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4906) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4906.1, data_13_4906.2]

/-- Complete interval computation for depth 13, residue 4907. -/
theorem bounds_13_4907 : exactInterval 13 4907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4907 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4907) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4907 : oddCount 4907 13 = 6 ∧ acceleratedOrbit 13 4907 = 437 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4907 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4907) = 3 ^ 6 * m + 437 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4907.1, data_13_4907.2]

/-- Complete interval computation for depth 13, residue 4908. -/
theorem bounds_13_4908 : exactInterval 13 4908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4908 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4908) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4908 : oddCount 4908 13 = 5 ∧ acceleratedOrbit 13 4908 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4908 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4908) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4908.1, data_13_4908.2]

/-- Complete interval computation for depth 13, residue 4909. -/
theorem bounds_13_4909 : exactInterval 13 4909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4909 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4909) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4909 : oddCount 4909 13 = 5 ∧ acceleratedOrbit 13 4909 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4909 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4909) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4909.1, data_13_4909.2]

/-- Complete interval computation for depth 13, residue 4910. -/
theorem bounds_13_4910 : exactInterval 13 4910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4910 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4910) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4910 : oddCount 4910 13 = 5 ∧ acceleratedOrbit 13 4910 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4910 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4910) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4910.1, data_13_4910.2]

/-- Complete interval computation for depth 13, residue 4911. -/
theorem bounds_13_4911 : exactInterval 13 4911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4911 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4911) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4911 : oddCount 4911 13 = 8 ∧ acceleratedOrbit 13 4911 = 3935 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4911 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4911) = 3 ^ 8 * m + 3935 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4911.1, data_13_4911.2]

/-- Complete interval computation for depth 13, residue 4912. -/
theorem bounds_13_4912 : exactInterval 13 4912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4912 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4912) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4912 : oddCount 4912 13 = 4 ∧ acceleratedOrbit 13 4912 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4912 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4912) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4912.1, data_13_4912.2]

/-- Complete interval computation for depth 13, residue 4913. -/
theorem bounds_13_4913 : exactInterval 13 4913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4913 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4913) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4913 : oddCount 4913 13 = 5 ∧ acceleratedOrbit 13 4913 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4913 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4913) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4913.1, data_13_4913.2]

/-- Complete interval computation for depth 13, residue 4914. -/
theorem bounds_13_4914 : exactInterval 13 4914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4914 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4914) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4914 : oddCount 4914 13 = 5 ∧ acceleratedOrbit 13 4914 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4914 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4914) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4914.1, data_13_4914.2]

/-- Complete interval computation for depth 13, residue 4915. -/
theorem bounds_13_4915 : exactInterval 13 4915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4915 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4915) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4915 : oddCount 4915 13 = 5 ∧ acceleratedOrbit 13 4915 = 146 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4915 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4915) = 3 ^ 5 * m + 146 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4915.1, data_13_4915.2]

/-- Complete interval computation for depth 13, residue 4916. -/
theorem bounds_13_4916 : exactInterval 13 4916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4916 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4916) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4916 : oddCount 4916 13 = 4 ∧ acceleratedOrbit 13 4916 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4916 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4916) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4916.1, data_13_4916.2]

/-- Complete interval computation for depth 13, residue 4917. -/
theorem bounds_13_4917 : exactInterval 13 4917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4917 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4917) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4917 : oddCount 4917 13 = 4 ∧ acceleratedOrbit 13 4917 = 49 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4917 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4917) = 3 ^ 4 * m + 49 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4917.1, data_13_4917.2]

/-- Complete interval computation for depth 13, residue 4918. -/
theorem bounds_13_4918 : exactInterval 13 4918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4918 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4918) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4918 : oddCount 4918 13 = 9 ∧ acceleratedOrbit 13 4918 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4918 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4918) = 3 ^ 9 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4918.1, data_13_4918.2]

/-- Complete interval computation for depth 13, residue 4919. -/
theorem bounds_13_4919 : exactInterval 13 4919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_4919 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 4919) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_4919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_4919 : oddCount 4919 13 = 9 ∧ acceleratedOrbit 13 4919 = 11825 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_4919 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 4919) = 3 ^ 9 * m + 11825 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_4919.1, data_13_4919.2]

end Collatz.Research.StoppingAtlas.Batch0787
