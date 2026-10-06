import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0333

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 10878. -/
theorem bounds_15_10878 : exactInterval 15 10878 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10878 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10878) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10878 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10878 : oddCount 10878 15 = 9 ∧ acceleratedOrbit 15 10878 = 6536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10878 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10878) = 3 ^ 9 * m + 6536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10878.1, data_15_10878.2]

/-- Complete interval computation for depth 15, residue 10879. -/
theorem bounds_15_10879 : exactInterval 15 10879 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10879 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10879) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10879 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10879 : oddCount 10879 15 = 11 ∧ acceleratedOrbit 15 10879 = 58819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10879 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10879) = 3 ^ 11 * m + 58819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10879.1, data_15_10879.2]

/-- Complete interval computation for depth 15, residue 10880. -/
theorem bounds_15_10880 : exactInterval 15 10880 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10880 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10880) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10880 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10880 : oddCount 10880 15 = 1 ∧ acceleratedOrbit 15 10880 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10880 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10880) = 3 ^ 1 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10880.1, data_15_10880.2]

/-- Complete interval computation for depth 15, residue 10881. -/
theorem bounds_15_10881 : exactInterval 15 10881 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10881 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10881) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10881 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10881 : oddCount 10881 15 = 10 ∧ acceleratedOrbit 15 10881 = 19615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10881 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10881) = 3 ^ 10 * m + 19615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10881.1, data_15_10881.2]

/-- Complete interval computation for depth 15, residue 10882. -/
theorem bounds_15_10882 : exactInterval 15 10882 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10882 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10882) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10882 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10882 : oddCount 10882 15 = 8 ∧ acceleratedOrbit 15 10882 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10882 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10882) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10882.1, data_15_10882.2]

/-- Complete interval computation for depth 15, residue 10883. -/
theorem bounds_15_10883 : exactInterval 15 10883 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10883 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10883) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10883 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10883 : oddCount 10883 15 = 8 ∧ acceleratedOrbit 15 10883 = 2186 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10883 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10883) = 3 ^ 8 * m + 2186 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10883.1, data_15_10883.2]

/-- Complete interval computation for depth 15, residue 10884. -/
theorem bounds_15_10884 : exactInterval 15 10884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10884 : oddCount 10884 15 = 8 ∧ acceleratedOrbit 15 10884 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10884) = 3 ^ 8 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10884.1, data_15_10884.2]

/-- Complete interval computation for depth 15, residue 10885. -/
theorem bounds_15_10885 : exactInterval 15 10885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10885 : oddCount 10885 15 = 8 ∧ acceleratedOrbit 15 10885 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10885) = 3 ^ 8 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10885.1, data_15_10885.2]

/-- Complete interval computation for depth 15, residue 10886. -/
theorem bounds_15_10886 : exactInterval 15 10886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10886 : oddCount 10886 15 = 8 ∧ acceleratedOrbit 15 10886 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10886) = 3 ^ 8 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10886.1, data_15_10886.2]

/-- Complete interval computation for depth 15, residue 10887. -/
theorem bounds_15_10887 : exactInterval 15 10887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10887 : oddCount 10887 15 = 7 ∧ acceleratedOrbit 15 10887 = 728 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10887) = 3 ^ 7 * m + 728 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10887.1, data_15_10887.2]

/-- Complete interval computation for depth 15, residue 10888. -/
theorem bounds_15_10888 : exactInterval 15 10888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10888 : oddCount 10888 15 = 9 ∧ acceleratedOrbit 15 10888 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10888) = 3 ^ 9 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10888.1, data_15_10888.2]

/-- Complete interval computation for depth 15, residue 10889. -/
theorem bounds_15_10889 : exactInterval 15 10889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10889 : oddCount 10889 15 = 10 ∧ acceleratedOrbit 15 10889 = 19628 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10889) = 3 ^ 10 * m + 19628 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10889.1, data_15_10889.2]

/-- Complete interval computation for depth 15, residue 10890. -/
theorem bounds_15_10890 : exactInterval 15 10890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10890 : oddCount 10890 15 = 9 ∧ acceleratedOrbit 15 10890 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10890) = 3 ^ 9 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10890.1, data_15_10890.2]

/-- Complete interval computation for depth 15, residue 10891. -/
theorem bounds_15_10891 : exactInterval 15 10891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10891 : oddCount 10891 15 = 8 ∧ acceleratedOrbit 15 10891 = 2182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10891) = 3 ^ 8 * m + 2182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10891.1, data_15_10891.2]

/-- Complete interval computation for depth 15, residue 10892. -/
theorem bounds_15_10892 : exactInterval 15 10892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10892 : oddCount 10892 15 = 9 ∧ acceleratedOrbit 15 10892 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10892) = 3 ^ 9 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10892.1, data_15_10892.2]

/-- Complete interval computation for depth 15, residue 10893. -/
theorem bounds_15_10893 : exactInterval 15 10893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10893 : oddCount 10893 15 = 9 ∧ acceleratedOrbit 15 10893 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10893) = 3 ^ 9 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10893.1, data_15_10893.2]

/-- Complete interval computation for depth 15, residue 10894. -/
theorem bounds_15_10894 : exactInterval 15 10894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10894 : oddCount 10894 15 = 11 ∧ acceleratedOrbit 15 10894 = 58913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10894) = 3 ^ 11 * m + 58913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10894.1, data_15_10894.2]

/-- Complete interval computation for depth 15, residue 10895. -/
theorem bounds_15_10895 : exactInterval 15 10895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10895 : oddCount 10895 15 = 11 ∧ acceleratedOrbit 15 10895 = 58913 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10895) = 3 ^ 11 * m + 58913 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10895.1, data_15_10895.2]

/-- Complete interval computation for depth 15, residue 10896. -/
theorem bounds_15_10896 : exactInterval 15 10896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10896 : oddCount 10896 15 = 10 ∧ acceleratedOrbit 15 10896 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10896) = 3 ^ 10 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10896.1, data_15_10896.2]

/-- Complete interval computation for depth 15, residue 10897. -/
theorem bounds_15_10897 : exactInterval 15 10897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10897 : oddCount 10897 15 = 9 ∧ acceleratedOrbit 15 10897 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10897) = 3 ^ 9 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10897.1, data_15_10897.2]

/-- Complete interval computation for depth 15, residue 10898. -/
theorem bounds_15_10898 : exactInterval 15 10898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10898 : oddCount 10898 15 = 9 ∧ acceleratedOrbit 15 10898 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10898) = 3 ^ 9 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10898.1, data_15_10898.2]

/-- Complete interval computation for depth 15, residue 10899. -/
theorem bounds_15_10899 : exactInterval 15 10899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10899 : oddCount 10899 15 = 9 ∧ acceleratedOrbit 15 10899 = 6551 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10899) = 3 ^ 9 * m + 6551 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10899.1, data_15_10899.2]

/-- Complete interval computation for depth 15, residue 10900. -/
theorem bounds_15_10900 : exactInterval 15 10900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10900 : oddCount 10900 15 = 10 ∧ acceleratedOrbit 15 10900 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10900) = 3 ^ 10 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10900.1, data_15_10900.2]

/-- Complete interval computation for depth 15, residue 10901. -/
theorem bounds_15_10901 : exactInterval 15 10901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10901 : oddCount 10901 15 = 10 ∧ acceleratedOrbit 15 10901 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10901) = 3 ^ 10 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10901.1, data_15_10901.2]

/-- Complete interval computation for depth 15, residue 10902. -/
theorem bounds_15_10902 : exactInterval 15 10902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10902 : oddCount 10902 15 = 9 ∧ acceleratedOrbit 15 10902 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10902) = 3 ^ 9 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10902.1, data_15_10902.2]

/-- Complete interval computation for depth 15, residue 10903. -/
theorem bounds_15_10903 : exactInterval 15 10903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10903 : oddCount 10903 15 = 9 ∧ acceleratedOrbit 15 10903 = 6560 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10903) = 3 ^ 9 * m + 6560 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10903.1, data_15_10903.2]

/-- Complete interval computation for depth 15, residue 10904. -/
theorem bounds_15_10904 : exactInterval 15 10904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10904 : oddCount 10904 15 = 10 ∧ acceleratedOrbit 15 10904 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10904) = 3 ^ 10 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10904.1, data_15_10904.2]

/-- Complete interval computation for depth 15, residue 10905. -/
theorem bounds_15_10905 : exactInterval 15 10905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10905 : oddCount 10905 15 = 9 ∧ acceleratedOrbit 15 10905 = 6554 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10905) = 3 ^ 9 * m + 6554 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10905.1, data_15_10905.2]

/-- Complete interval computation for depth 15, residue 10906. -/
theorem bounds_15_10906 : exactInterval 15 10906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10906 : oddCount 10906 15 = 10 ∧ acceleratedOrbit 15 10906 = 19682 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10906) = 3 ^ 10 * m + 19682 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10906.1, data_15_10906.2]

/-- Complete interval computation for depth 15, residue 10907. -/
theorem bounds_15_10907 : exactInterval 15 10907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10907 : oddCount 10907 15 = 10 ∧ acceleratedOrbit 15 10907 = 19658 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10907) = 3 ^ 10 * m + 19658 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10907.1, data_15_10907.2]

/-- Complete interval computation for depth 15, residue 10908. -/
theorem bounds_15_10908 : exactInterval 15 10908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10908 : oddCount 10908 15 = 9 ∧ acceleratedOrbit 15 10908 = 6556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10908) = 3 ^ 9 * m + 6556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10908.1, data_15_10908.2]

/-- Complete interval computation for depth 15, residue 10909. -/
theorem bounds_15_10909 : exactInterval 15 10909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10909 : oddCount 10909 15 = 9 ∧ acceleratedOrbit 15 10909 = 6556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10909) = 3 ^ 9 * m + 6556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10909.1, data_15_10909.2]

/-- Complete interval computation for depth 15, residue 10910. -/
theorem bounds_15_10910 : exactInterval 15 10910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_10910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 10910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_10910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_10910 : oddCount 10910 15 = 9 ∧ acceleratedOrbit 15 10910 = 6556 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_10910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 10910) = 3 ^ 9 * m + 6556 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_10910.1, data_15_10910.2]

end Collatz.Research.PassageAtlas.Batch0333
