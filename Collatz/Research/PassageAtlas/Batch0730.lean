import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0730

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 23887. -/
theorem bounds_15_23887 : exactInterval 15 23887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23887 : oddCount 23887 15 = 9 ∧ acceleratedOrbit 15 23887 = 14350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23887) = 3 ^ 9 * m + 14350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23887.1, data_15_23887.2]

/-- Complete interval computation for depth 15, residue 23888. -/
theorem bounds_15_23888 : exactInterval 15 23888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23888 : oddCount 23888 15 = 3 ∧ acceleratedOrbit 15 23888 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23888) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23888.1, data_15_23888.2]

/-- Complete interval computation for depth 15, residue 23889. -/
theorem bounds_15_23889 : exactInterval 15 23889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23889 : oddCount 23889 15 = 8 ∧ acceleratedOrbit 15 23889 = 4784 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23889) = 3 ^ 8 * m + 4784 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23889.1, data_15_23889.2]

/-- Complete interval computation for depth 15, residue 23890. -/
theorem bounds_15_23890 : exactInterval 15 23890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23890 : oddCount 23890 15 = 11 ∧ acceleratedOrbit 15 23890 = 129170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23890) = 3 ^ 11 * m + 129170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23890.1, data_15_23890.2]

/-- Complete interval computation for depth 15, residue 23891. -/
theorem bounds_15_23891 : exactInterval 15 23891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23891 : oddCount 23891 15 = 11 ∧ acceleratedOrbit 15 23891 = 129170 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23891) = 3 ^ 11 * m + 129170 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23891.1, data_15_23891.2]

/-- Complete interval computation for depth 15, residue 23892. -/
theorem bounds_15_23892 : exactInterval 15 23892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23892 : oddCount 23892 15 = 3 ∧ acceleratedOrbit 15 23892 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23892) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23892.1, data_15_23892.2]

/-- Complete interval computation for depth 15, residue 23893. -/
theorem bounds_15_23893 : exactInterval 15 23893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23893 : oddCount 23893 15 = 3 ∧ acceleratedOrbit 15 23893 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23893) = 3 ^ 3 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23893.1, data_15_23893.2]

/-- Complete interval computation for depth 15, residue 23894. -/
theorem bounds_15_23894 : exactInterval 15 23894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23894 : oddCount 23894 15 = 9 ∧ acceleratedOrbit 15 23894 = 14357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23894) = 3 ^ 9 * m + 14357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23894.1, data_15_23894.2]

/-- Complete interval computation for depth 15, residue 23895. -/
theorem bounds_15_23895 : exactInterval 15 23895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23895 : oddCount 23895 15 = 9 ∧ acceleratedOrbit 15 23895 = 14357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23895) = 3 ^ 9 * m + 14357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23895.1, data_15_23895.2]

/-- Complete interval computation for depth 15, residue 23896. -/
theorem bounds_15_23896 : exactInterval 15 23896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23896 : oddCount 23896 15 = 6 ∧ acceleratedOrbit 15 23896 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23896) = 3 ^ 6 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23896.1, data_15_23896.2]

/-- Complete interval computation for depth 15, residue 23897. -/
theorem bounds_15_23897 : exactInterval 15 23897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23897 : oddCount 23897 15 = 6 ∧ acceleratedOrbit 15 23897 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23897) = 3 ^ 6 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23897.1, data_15_23897.2]

/-- Complete interval computation for depth 15, residue 23898. -/
theorem bounds_15_23898 : exactInterval 15 23898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23898 : oddCount 23898 15 = 6 ∧ acceleratedOrbit 15 23898 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23898) = 3 ^ 6 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23898.1, data_15_23898.2]

/-- Complete interval computation for depth 15, residue 23899. -/
theorem bounds_15_23899 : exactInterval 15 23899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23899 : oddCount 23899 15 = 9 ∧ acceleratedOrbit 15 23899 = 14357 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23899) = 3 ^ 9 * m + 14357 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23899.1, data_15_23899.2]

/-- Complete interval computation for depth 15, residue 23900. -/
theorem bounds_15_23900 : exactInterval 15 23900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23900 : oddCount 23900 15 = 6 ∧ acceleratedOrbit 15 23900 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23900) = 3 ^ 6 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23900.1, data_15_23900.2]

/-- Complete interval computation for depth 15, residue 23901. -/
theorem bounds_15_23901 : exactInterval 15 23901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23901 : oddCount 23901 15 = 6 ∧ acceleratedOrbit 15 23901 = 532 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23901) = 3 ^ 6 * m + 532 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23901.1, data_15_23901.2]

/-- Complete interval computation for depth 15, residue 23902. -/
theorem bounds_15_23902 : exactInterval 15 23902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23902 : oddCount 23902 15 = 8 ∧ acceleratedOrbit 15 23902 = 4787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23902) = 3 ^ 8 * m + 4787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23902.1, data_15_23902.2]

/-- Complete interval computation for depth 15, residue 23903. -/
theorem bounds_15_23903 : exactInterval 15 23903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23903 : oddCount 23903 15 = 8 ∧ acceleratedOrbit 15 23903 = 4787 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23903) = 3 ^ 8 * m + 4787 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23903.1, data_15_23903.2]

/-- Complete interval computation for depth 15, residue 23904. -/
theorem bounds_15_23904 : exactInterval 15 23904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23904 : oddCount 23904 15 = 6 ∧ acceleratedOrbit 15 23904 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23904) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23904.1, data_15_23904.2]

/-- Complete interval computation for depth 15, residue 23905. -/
theorem bounds_15_23905 : exactInterval 15 23905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23905 : oddCount 23905 15 = 9 ∧ acceleratedOrbit 15 23905 = 14363 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23905) = 3 ^ 9 * m + 14363 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23905.1, data_15_23905.2]

/-- Complete interval computation for depth 15, residue 23906. -/
theorem bounds_15_23906 : exactInterval 15 23906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23906 : oddCount 23906 15 = 6 ∧ acceleratedOrbit 15 23906 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23906) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23906.1, data_15_23906.2]

/-- Complete interval computation for depth 15, residue 23907. -/
theorem bounds_15_23907 : exactInterval 15 23907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23907 : oddCount 23907 15 = 6 ∧ acceleratedOrbit 15 23907 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23907) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23907.1, data_15_23907.2]

/-- Complete interval computation for depth 15, residue 23908. -/
theorem bounds_15_23908 : exactInterval 15 23908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23908 : oddCount 23908 15 = 6 ∧ acceleratedOrbit 15 23908 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23908) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23908.1, data_15_23908.2]

/-- Complete interval computation for depth 15, residue 23909. -/
theorem bounds_15_23909 : exactInterval 15 23909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23909 : oddCount 23909 15 = 6 ∧ acceleratedOrbit 15 23909 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23909) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23909.1, data_15_23909.2]

/-- Complete interval computation for depth 15, residue 23910. -/
theorem bounds_15_23910 : exactInterval 15 23910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23910 : oddCount 23910 15 = 6 ∧ acceleratedOrbit 15 23910 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23910) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23910.1, data_15_23910.2]

/-- Complete interval computation for depth 15, residue 23911. -/
theorem bounds_15_23911 : exactInterval 15 23911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23911 : oddCount 23911 15 = 12 ∧ acceleratedOrbit 15 23911 = 387818 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23911) = 3 ^ 12 * m + 387818 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23911.1, data_15_23911.2]

/-- Complete interval computation for depth 15, residue 23912. -/
theorem bounds_15_23912 : exactInterval 15 23912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23912 : oddCount 23912 15 = 6 ∧ acceleratedOrbit 15 23912 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23912) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23912.1, data_15_23912.2]

/-- Complete interval computation for depth 15, residue 23913. -/
theorem bounds_15_23913 : exactInterval 15 23913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23913 : oddCount 23913 15 = 8 ∧ acceleratedOrbit 15 23913 = 4789 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23913) = 3 ^ 8 * m + 4789 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23913.1, data_15_23913.2]

/-- Complete interval computation for depth 15, residue 23914. -/
theorem bounds_15_23914 : exactInterval 15 23914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23914 : oddCount 23914 15 = 6 ∧ acceleratedOrbit 15 23914 = 533 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23914) = 3 ^ 6 * m + 533 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23914.1, data_15_23914.2]

/-- Complete interval computation for depth 15, residue 23915. -/
theorem bounds_15_23915 : exactInterval 15 23915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23915 : oddCount 23915 15 = 8 ∧ acceleratedOrbit 15 23915 = 4789 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23915) = 3 ^ 8 * m + 4789 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23915.1, data_15_23915.2]

/-- Complete interval computation for depth 15, residue 23916. -/
theorem bounds_15_23916 : exactInterval 15 23916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23916 : oddCount 23916 15 = 8 ∧ acceleratedOrbit 15 23916 = 4790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23916) = 3 ^ 8 * m + 4790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23916.1, data_15_23916.2]

/-- Complete interval computation for depth 15, residue 23917. -/
theorem bounds_15_23917 : exactInterval 15 23917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23917 : oddCount 23917 15 = 8 ∧ acceleratedOrbit 15 23917 = 4790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23917) = 3 ^ 8 * m + 4790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23917.1, data_15_23917.2]

/-- Complete interval computation for depth 15, residue 23918. -/
theorem bounds_15_23918 : exactInterval 15 23918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23918 : oddCount 23918 15 = 8 ∧ acceleratedOrbit 15 23918 = 4790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23918) = 3 ^ 8 * m + 4790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23918.1, data_15_23918.2]

/-- Complete interval computation for depth 15, residue 23919. -/
theorem bounds_15_23919 : exactInterval 15 23919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_23919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 23919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_23919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_23919 : oddCount 23919 15 = 8 ∧ acceleratedOrbit 15 23919 = 4790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_23919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 23919) = 3 ^ 8 * m + 4790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_23919.1, data_15_23919.2]

end Collatz.Research.PassageAtlas.Batch0730
