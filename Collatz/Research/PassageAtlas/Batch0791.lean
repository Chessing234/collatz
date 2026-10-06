import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0791

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 25886. -/
theorem bounds_15_25886 : exactInterval 15 25886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25886 : oddCount 25886 15 = 11 ∧ acceleratedOrbit 15 25886 = 139967 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25886) = 3 ^ 11 * m + 139967 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25886.1, data_15_25886.2]

/-- Complete interval computation for depth 15, residue 25887. -/
theorem bounds_15_25887 : exactInterval 15 25887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25887 : oddCount 25887 15 = 10 ∧ acceleratedOrbit 15 25887 = 46655 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25887) = 3 ^ 10 * m + 46655 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25887.1, data_15_25887.2]

/-- Complete interval computation for depth 15, residue 25888. -/
theorem bounds_15_25888 : exactInterval 15 25888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25888 : oddCount 25888 15 = 6 ∧ acceleratedOrbit 15 25888 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25888) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25888.1, data_15_25888.2]

/-- Complete interval computation for depth 15, residue 25889. -/
theorem bounds_15_25889 : exactInterval 15 25889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25889 : oddCount 25889 15 = 4 ∧ acceleratedOrbit 15 25889 = 64 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25889) = 3 ^ 4 * m + 64 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25889.1, data_15_25889.2]

/-- Complete interval computation for depth 15, residue 25890. -/
theorem bounds_15_25890 : exactInterval 15 25890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25890 : oddCount 25890 15 = 7 ∧ acceleratedOrbit 15 25890 = 1729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25890) = 3 ^ 7 * m + 1729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25890.1, data_15_25890.2]

/-- Complete interval computation for depth 15, residue 25891. -/
theorem bounds_15_25891 : exactInterval 15 25891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25891 : oddCount 25891 15 = 7 ∧ acceleratedOrbit 15 25891 = 1729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25891) = 3 ^ 7 * m + 1729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25891.1, data_15_25891.2]

/-- Complete interval computation for depth 15, residue 25892. -/
theorem bounds_15_25892 : exactInterval 15 25892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25892 : oddCount 25892 15 = 7 ∧ acceleratedOrbit 15 25892 = 1729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25892) = 3 ^ 7 * m + 1729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25892.1, data_15_25892.2]

/-- Complete interval computation for depth 15, residue 25893. -/
theorem bounds_15_25893 : exactInterval 15 25893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25893 : oddCount 25893 15 = 7 ∧ acceleratedOrbit 15 25893 = 1729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25893) = 3 ^ 7 * m + 1729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25893.1, data_15_25893.2]

/-- Complete interval computation for depth 15, residue 25894. -/
theorem bounds_15_25894 : exactInterval 15 25894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25894 : oddCount 25894 15 = 7 ∧ acceleratedOrbit 15 25894 = 1729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25894) = 3 ^ 7 * m + 1729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25894.1, data_15_25894.2]

/-- Complete interval computation for depth 15, residue 25895. -/
theorem bounds_15_25895 : exactInterval 15 25895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25895 : oddCount 25895 15 = 8 ∧ acceleratedOrbit 15 25895 = 5186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25895) = 3 ^ 8 * m + 5186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25895.1, data_15_25895.2]

/-- Complete interval computation for depth 15, residue 25896. -/
theorem bounds_15_25896 : exactInterval 15 25896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25896 : oddCount 25896 15 = 6 ∧ acceleratedOrbit 15 25896 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25896) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25896.1, data_15_25896.2]

/-- Complete interval computation for depth 15, residue 25897. -/
theorem bounds_15_25897 : exactInterval 15 25897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25897 : oddCount 25897 15 = 9 ∧ acceleratedOrbit 15 25897 = 15557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25897) = 3 ^ 9 * m + 15557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25897.1, data_15_25897.2]

/-- Complete interval computation for depth 15, residue 25898. -/
theorem bounds_15_25898 : exactInterval 15 25898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25898 : oddCount 25898 15 = 6 ∧ acceleratedOrbit 15 25898 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25898) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25898.1, data_15_25898.2]

/-- Complete interval computation for depth 15, residue 25899. -/
theorem bounds_15_25899 : exactInterval 15 25899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25899 : oddCount 25899 15 = 7 ∧ acceleratedOrbit 15 25899 = 1729 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25899) = 3 ^ 7 * m + 1729 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25899.1, data_15_25899.2]

/-- Complete interval computation for depth 15, residue 25900. -/
theorem bounds_15_25900 : exactInterval 15 25900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25900 : oddCount 25900 15 = 6 ∧ acceleratedOrbit 15 25900 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25900) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25900.1, data_15_25900.2]

/-- Complete interval computation for depth 15, residue 25901. -/
theorem bounds_15_25901 : exactInterval 15 25901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25901 : oddCount 25901 15 = 6 ∧ acceleratedOrbit 15 25901 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25901) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25901.1, data_15_25901.2]

/-- Complete interval computation for depth 15, residue 25902. -/
theorem bounds_15_25902 : exactInterval 15 25902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25902 : oddCount 25902 15 = 6 ∧ acceleratedOrbit 15 25902 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25902) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25902.1, data_15_25902.2]

/-- Complete interval computation for depth 15, residue 25903. -/
theorem bounds_15_25903 : exactInterval 15 25903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25903 : oddCount 25903 15 = 10 ∧ acceleratedOrbit 15 25903 = 46682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25903) = 3 ^ 10 * m + 46682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25903.1, data_15_25903.2]

/-- Complete interval computation for depth 15, residue 25904. -/
theorem bounds_15_25904 : exactInterval 15 25904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25904 : oddCount 25904 15 = 6 ∧ acceleratedOrbit 15 25904 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25904) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25904.1, data_15_25904.2]

/-- Complete interval computation for depth 15, residue 25905. -/
theorem bounds_15_25905 : exactInterval 15 25905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25905 : oddCount 25905 15 = 7 ∧ acceleratedOrbit 15 25905 = 1730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25905) = 3 ^ 7 * m + 1730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25905.1, data_15_25905.2]

/-- Complete interval computation for depth 15, residue 25906. -/
theorem bounds_15_25906 : exactInterval 15 25906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25906 : oddCount 25906 15 = 7 ∧ acceleratedOrbit 15 25906 = 1730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25906) = 3 ^ 7 * m + 1730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25906.1, data_15_25906.2]

/-- Complete interval computation for depth 15, residue 25907. -/
theorem bounds_15_25907 : exactInterval 15 25907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25907 : oddCount 25907 15 = 7 ∧ acceleratedOrbit 15 25907 = 1730 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25907) = 3 ^ 7 * m + 1730 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25907.1, data_15_25907.2]

/-- Complete interval computation for depth 15, residue 25908. -/
theorem bounds_15_25908 : exactInterval 15 25908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25908 : oddCount 25908 15 = 6 ∧ acceleratedOrbit 15 25908 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25908) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25908.1, data_15_25908.2]

/-- Complete interval computation for depth 15, residue 25909. -/
theorem bounds_15_25909 : exactInterval 15 25909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25909 : oddCount 25909 15 = 6 ∧ acceleratedOrbit 15 25909 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25909) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25909.1, data_15_25909.2]

/-- Complete interval computation for depth 15, residue 25910. -/
theorem bounds_15_25910 : exactInterval 15 25910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25910 : oddCount 25910 15 = 11 ∧ acceleratedOrbit 15 25910 = 140089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25910) = 3 ^ 11 * m + 140089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25910.1, data_15_25910.2]

/-- Complete interval computation for depth 15, residue 25911. -/
theorem bounds_15_25911 : exactInterval 15 25911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25911 : oddCount 25911 15 = 11 ∧ acceleratedOrbit 15 25911 = 140089 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25911) = 3 ^ 11 * m + 140089 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25911.1, data_15_25911.2]

/-- Complete interval computation for depth 15, residue 25912. -/
theorem bounds_15_25912 : exactInterval 15 25912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25912 : oddCount 25912 15 = 9 ∧ acceleratedOrbit 15 25912 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25912) = 3 ^ 9 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25912.1, data_15_25912.2]

/-- Complete interval computation for depth 15, residue 25913. -/
theorem bounds_15_25913 : exactInterval 15 25913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25913 : oddCount 25913 15 = 8 ∧ acceleratedOrbit 15 25913 = 5189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25913) = 3 ^ 8 * m + 5189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25913.1, data_15_25913.2]

/-- Complete interval computation for depth 15, residue 25914. -/
theorem bounds_15_25914 : exactInterval 15 25914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25914 : oddCount 25914 15 = 9 ∧ acceleratedOrbit 15 25914 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25914) = 3 ^ 9 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25914.1, data_15_25914.2]

/-- Complete interval computation for depth 15, residue 25915. -/
theorem bounds_15_25915 : exactInterval 15 25915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25915 : oddCount 25915 15 = 6 ∧ acceleratedOrbit 15 25915 = 577 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25915) = 3 ^ 6 * m + 577 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25915.1, data_15_25915.2]

/-- Complete interval computation for depth 15, residue 25916. -/
theorem bounds_15_25916 : exactInterval 15 25916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25916 : oddCount 25916 15 = 9 ∧ acceleratedOrbit 15 25916 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25916) = 3 ^ 9 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25916.1, data_15_25916.2]

/-- Complete interval computation for depth 15, residue 25917. -/
theorem bounds_15_25917 : exactInterval 15 25917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25917 : oddCount 25917 15 = 9 ∧ acceleratedOrbit 15 25917 = 15572 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25917) = 3 ^ 9 * m + 15572 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25917.1, data_15_25917.2]

/-- Complete interval computation for depth 15, residue 25918. -/
theorem bounds_15_25918 : exactInterval 15 25918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_25918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 25918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_25918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_25918 : oddCount 25918 15 = 11 ∧ acceleratedOrbit 15 25918 = 140129 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_25918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 25918) = 3 ^ 11 * m + 140129 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_25918.1, data_15_25918.2]

end Collatz.Research.PassageAtlas.Batch0791
