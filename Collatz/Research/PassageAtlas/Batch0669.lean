import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0669

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21889. -/
theorem bounds_15_21889 : exactInterval 15 21889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21889 : oddCount 21889 15 = 8 ∧ acceleratedOrbit 15 21889 = 4384 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21889) = 3 ^ 8 * m + 4384 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21889.1, data_15_21889.2]

/-- Complete interval computation for depth 15, residue 21890. -/
theorem bounds_15_21890 : exactInterval 15 21890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21890 : oddCount 21890 15 = 6 ∧ acceleratedOrbit 15 21890 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21890) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21890.1, data_15_21890.2]

/-- Complete interval computation for depth 15, residue 21891. -/
theorem bounds_15_21891 : exactInterval 15 21891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21891 : oddCount 21891 15 = 6 ∧ acceleratedOrbit 15 21891 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21891) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21891.1, data_15_21891.2]

/-- Complete interval computation for depth 15, residue 21892. -/
theorem bounds_15_21892 : exactInterval 15 21892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21892 : oddCount 21892 15 = 7 ∧ acceleratedOrbit 15 21892 = 1462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21892) = 3 ^ 7 * m + 1462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21892.1, data_15_21892.2]

/-- Complete interval computation for depth 15, residue 21893. -/
theorem bounds_15_21893 : exactInterval 15 21893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21893 : oddCount 21893 15 = 7 ∧ acceleratedOrbit 15 21893 = 1462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21893) = 3 ^ 7 * m + 1462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21893.1, data_15_21893.2]

/-- Complete interval computation for depth 15, residue 21894. -/
theorem bounds_15_21894 : exactInterval 15 21894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21894 : oddCount 21894 15 = 7 ∧ acceleratedOrbit 15 21894 = 1462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21894) = 3 ^ 7 * m + 1462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21894.1, data_15_21894.2]

/-- Complete interval computation for depth 15, residue 21895. -/
theorem bounds_15_21895 : exactInterval 15 21895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21895 : oddCount 21895 15 = 6 ∧ acceleratedOrbit 15 21895 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21895) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21895.1, data_15_21895.2]

/-- Complete interval computation for depth 15, residue 21896. -/
theorem bounds_15_21896 : exactInterval 15 21896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21896 : oddCount 21896 15 = 5 ∧ acceleratedOrbit 15 21896 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21896) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21896.1, data_15_21896.2]

/-- Complete interval computation for depth 15, residue 21897. -/
theorem bounds_15_21897 : exactInterval 15 21897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21897 : oddCount 21897 15 = 8 ∧ acceleratedOrbit 15 21897 = 4385 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21897) = 3 ^ 8 * m + 4385 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21897.1, data_15_21897.2]

/-- Complete interval computation for depth 15, residue 21898. -/
theorem bounds_15_21898 : exactInterval 15 21898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21898 : oddCount 21898 15 = 5 ∧ acceleratedOrbit 15 21898 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21898) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21898.1, data_15_21898.2]

/-- Complete interval computation for depth 15, residue 21899. -/
theorem bounds_15_21899 : exactInterval 15 21899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21899 : oddCount 21899 15 = 7 ∧ acceleratedOrbit 15 21899 = 1462 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21899) = 3 ^ 7 * m + 1462 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21899.1, data_15_21899.2]

/-- Complete interval computation for depth 15, residue 21900. -/
theorem bounds_15_21900 : exactInterval 15 21900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21900 : oddCount 21900 15 = 5 ∧ acceleratedOrbit 15 21900 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21900) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21900.1, data_15_21900.2]

/-- Complete interval computation for depth 15, residue 21901. -/
theorem bounds_15_21901 : exactInterval 15 21901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21901 : oddCount 21901 15 = 5 ∧ acceleratedOrbit 15 21901 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21901) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21901.1, data_15_21901.2]

/-- Complete interval computation for depth 15, residue 21902. -/
theorem bounds_15_21902 : exactInterval 15 21902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21902 : oddCount 21902 15 = 8 ∧ acceleratedOrbit 15 21902 = 4387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21902) = 3 ^ 8 * m + 4387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21902.1, data_15_21902.2]

/-- Complete interval computation for depth 15, residue 21903. -/
theorem bounds_15_21903 : exactInterval 15 21903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21903 : oddCount 21903 15 = 8 ∧ acceleratedOrbit 15 21903 = 4387 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21903) = 3 ^ 8 * m + 4387 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21903.1, data_15_21903.2]

/-- Complete interval computation for depth 15, residue 21904. -/
theorem bounds_15_21904 : exactInterval 15 21904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21904 : oddCount 21904 15 = 5 ∧ acceleratedOrbit 15 21904 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21904) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21904.1, data_15_21904.2]

/-- Complete interval computation for depth 15, residue 21905. -/
theorem bounds_15_21905 : exactInterval 15 21905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21905 : oddCount 21905 15 = 6 ∧ acceleratedOrbit 15 21905 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21905) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21905.1, data_15_21905.2]

/-- Complete interval computation for depth 15, residue 21906. -/
theorem bounds_15_21906 : exactInterval 15 21906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21906 : oddCount 21906 15 = 6 ∧ acceleratedOrbit 15 21906 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21906) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21906.1, data_15_21906.2]

/-- Complete interval computation for depth 15, residue 21907. -/
theorem bounds_15_21907 : exactInterval 15 21907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21907 : oddCount 21907 15 = 6 ∧ acceleratedOrbit 15 21907 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21907) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21907.1, data_15_21907.2]

/-- Complete interval computation for depth 15, residue 21908. -/
theorem bounds_15_21908 : exactInterval 15 21908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21908 : oddCount 21908 15 = 5 ∧ acceleratedOrbit 15 21908 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21908) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21908.1, data_15_21908.2]

/-- Complete interval computation for depth 15, residue 21909. -/
theorem bounds_15_21909 : exactInterval 15 21909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21909 : oddCount 21909 15 = 5 ∧ acceleratedOrbit 15 21909 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21909) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21909.1, data_15_21909.2]

/-- Complete interval computation for depth 15, residue 21910. -/
theorem bounds_15_21910 : exactInterval 15 21910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21910 : oddCount 21910 15 = 7 ∧ acceleratedOrbit 15 21910 = 1463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21910) = 3 ^ 7 * m + 1463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21910.1, data_15_21910.2]

/-- Complete interval computation for depth 15, residue 21911. -/
theorem bounds_15_21911 : exactInterval 15 21911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21911 : oddCount 21911 15 = 7 ∧ acceleratedOrbit 15 21911 = 1463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21911) = 3 ^ 7 * m + 1463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21911.1, data_15_21911.2]

/-- Complete interval computation for depth 15, residue 21912. -/
theorem bounds_15_21912 : exactInterval 15 21912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21912 : oddCount 21912 15 = 5 ∧ acceleratedOrbit 15 21912 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21912) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21912.1, data_15_21912.2]

/-- Complete interval computation for depth 15, residue 21913. -/
theorem bounds_15_21913 : exactInterval 15 21913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21913 : oddCount 21913 15 = 7 ∧ acceleratedOrbit 15 21913 = 1463 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21913) = 3 ^ 7 * m + 1463 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21913.1, data_15_21913.2]

/-- Complete interval computation for depth 15, residue 21914. -/
theorem bounds_15_21914 : exactInterval 15 21914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21914 : oddCount 21914 15 = 5 ∧ acceleratedOrbit 15 21914 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21914) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21914.1, data_15_21914.2]

/-- Complete interval computation for depth 15, residue 21915. -/
theorem bounds_15_21915 : exactInterval 15 21915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21915 : oddCount 21915 15 = 9 ∧ acceleratedOrbit 15 21915 = 13166 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21915) = 3 ^ 9 * m + 13166 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21915.1, data_15_21915.2]

/-- Complete interval computation for depth 15, residue 21916. -/
theorem bounds_15_21916 : exactInterval 15 21916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21916 : oddCount 21916 15 = 10 ∧ acceleratedOrbit 15 21916 = 39503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21916) = 3 ^ 10 * m + 39503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21916.1, data_15_21916.2]

/-- Complete interval computation for depth 15, residue 21917. -/
theorem bounds_15_21917 : exactInterval 15 21917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21917 : oddCount 21917 15 = 10 ∧ acceleratedOrbit 15 21917 = 39503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21917) = 3 ^ 10 * m + 39503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21917.1, data_15_21917.2]

/-- Complete interval computation for depth 15, residue 21918. -/
theorem bounds_15_21918 : exactInterval 15 21918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21918 : oddCount 21918 15 = 10 ∧ acceleratedOrbit 15 21918 = 39503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21918) = 3 ^ 10 * m + 39503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21918.1, data_15_21918.2]

/-- Complete interval computation for depth 15, residue 21919. -/
theorem bounds_15_21919 : exactInterval 15 21919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21919 : oddCount 21919 15 = 13 ∧ acceleratedOrbit 15 21919 = 1066526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21919) = 3 ^ 13 * m + 1066526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21919.1, data_15_21919.2]

/-- Complete interval computation for depth 15, residue 21920. -/
theorem bounds_15_21920 : exactInterval 15 21920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21920 : oddCount 21920 15 = 5 ∧ acceleratedOrbit 15 21920 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21920) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21920.1, data_15_21920.2]

end Collatz.Research.PassageAtlas.Batch0669
