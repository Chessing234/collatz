import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0028

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 884. -/
theorem bounds_15_884 : exactInterval 15 884 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_884 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 884) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_884 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_884 : oddCount 884 15 = 8 ∧ acceleratedOrbit 15 884 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_884 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 884) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_884.1, data_15_884.2]

/-- Complete interval computation for depth 15, residue 885. -/
theorem bounds_15_885 : exactInterval 15 885 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_885 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 885) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_885 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_885 : oddCount 885 15 = 8 ∧ acceleratedOrbit 15 885 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_885 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 885) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_885.1, data_15_885.2]

/-- Complete interval computation for depth 15, residue 886. -/
theorem bounds_15_886 : exactInterval 15 886 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_886 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 886) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_886 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_886 : oddCount 886 15 = 8 ∧ acceleratedOrbit 15 886 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_886 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 886) = 3 ^ 8 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_886.1, data_15_886.2]

/-- Complete interval computation for depth 15, residue 887. -/
theorem bounds_15_887 : exactInterval 15 887 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_887 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 887) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_887 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_887 : oddCount 887 15 = 8 ∧ acceleratedOrbit 15 887 = 179 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_887 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 887) = 3 ^ 8 * m + 179 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_887.1, data_15_887.2]

/-- Complete interval computation for depth 15, residue 888. -/
theorem bounds_15_888 : exactInterval 15 888 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_888 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 888) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_888 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_888 : oddCount 888 15 = 10 ∧ acceleratedOrbit 15 888 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_888 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 888) = 3 ^ 10 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_888.1, data_15_888.2]

/-- Complete interval computation for depth 15, residue 889. -/
theorem bounds_15_889 : exactInterval 15 889 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_889 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 889) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_889 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_889 : oddCount 889 15 = 11 ∧ acceleratedOrbit 15 889 = 4819 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_889 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 889) = 3 ^ 11 * m + 4819 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_889.1, data_15_889.2]

/-- Complete interval computation for depth 15, residue 890. -/
theorem bounds_15_890 : exactInterval 15 890 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_890 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 890) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_890 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_890 : oddCount 890 15 = 10 ∧ acceleratedOrbit 15 890 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_890 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 890) = 3 ^ 10 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_890.1, data_15_890.2]

/-- Complete interval computation for depth 15, residue 891. -/
theorem bounds_15_891 : exactInterval 15 891 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_891 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 891) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_891 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_891 : oddCount 891 15 = 10 ∧ acceleratedOrbit 15 891 = 1610 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_891 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 891) = 3 ^ 10 * m + 1610 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_891.1, data_15_891.2]

/-- Complete interval computation for depth 15, residue 892. -/
theorem bounds_15_892 : exactInterval 15 892 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_892 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 892) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_892 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_892 : oddCount 892 15 = 10 ∧ acceleratedOrbit 15 892 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_892 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 892) = 3 ^ 10 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_892.1, data_15_892.2]

/-- Complete interval computation for depth 15, residue 893. -/
theorem bounds_15_893 : exactInterval 15 893 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_893 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 893) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_893 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_893 : oddCount 893 15 = 10 ∧ acceleratedOrbit 15 893 = 1619 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_893 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 893) = 3 ^ 10 * m + 1619 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_893.1, data_15_893.2]

/-- Complete interval computation for depth 15, residue 894. -/
theorem bounds_15_894 : exactInterval 15 894 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_894 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 894) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_894 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_894 : oddCount 894 15 = 10 ∧ acceleratedOrbit 15 894 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_894 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 894) = 3 ^ 10 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_894.1, data_15_894.2]

/-- Complete interval computation for depth 15, residue 895. -/
theorem bounds_15_895 : exactInterval 15 895 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_895 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 895) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_895 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_895 : oddCount 895 15 = 10 ∧ acceleratedOrbit 15 895 = 1615 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_895 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 895) = 3 ^ 10 * m + 1615 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_895.1, data_15_895.2]

/-- Complete interval computation for depth 15, residue 896. -/
theorem bounds_15_896 : exactInterval 15 896 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_896 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 896) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_896 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_896 : oddCount 896 15 = 5 ∧ acceleratedOrbit 15 896 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_896 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 896) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_896.1, data_15_896.2]

/-- Complete interval computation for depth 15, residue 897. -/
theorem bounds_15_897 : exactInterval 15 897 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_897 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 897) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_897 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_897 : oddCount 897 15 = 9 ∧ acceleratedOrbit 15 897 = 542 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_897 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 897) = 3 ^ 9 * m + 542 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_897.1, data_15_897.2]

/-- Complete interval computation for depth 15, residue 898. -/
theorem bounds_15_898 : exactInterval 15 898 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_898 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 898) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_898 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_898 : oddCount 898 15 = 8 ∧ acceleratedOrbit 15 898 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_898 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 898) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_898.1, data_15_898.2]

/-- Complete interval computation for depth 15, residue 899. -/
theorem bounds_15_899 : exactInterval 15 899 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_899 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 899) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_899 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_899 : oddCount 899 15 = 8 ∧ acceleratedOrbit 15 899 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_899 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 899) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_899.1, data_15_899.2]

/-- Complete interval computation for depth 15, residue 900. -/
theorem bounds_15_900 : exactInterval 15 900 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_900 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 900) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_900 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_900 : oddCount 900 15 = 10 ∧ acceleratedOrbit 15 900 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_900 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 900) = 3 ^ 10 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_900.1, data_15_900.2]

/-- Complete interval computation for depth 15, residue 901. -/
theorem bounds_15_901 : exactInterval 15 901 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_901 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 901) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_901 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_901 : oddCount 901 15 = 10 ∧ acceleratedOrbit 15 901 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_901 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 901) = 3 ^ 10 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_901.1, data_15_901.2]

/-- Complete interval computation for depth 15, residue 902. -/
theorem bounds_15_902 : exactInterval 15 902 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_902 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 902) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_902 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_902 : oddCount 902 15 = 10 ∧ acceleratedOrbit 15 902 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_902 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 902) = 3 ^ 10 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_902.1, data_15_902.2]

/-- Complete interval computation for depth 15, residue 903. -/
theorem bounds_15_903 : exactInterval 15 903 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_903 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 903) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_903 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_903 : oddCount 903 15 = 8 ∧ acceleratedOrbit 15 903 = 182 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_903 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 903) = 3 ^ 8 * m + 182 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_903.1, data_15_903.2]

/-- Complete interval computation for depth 15, residue 904. -/
theorem bounds_15_904 : exactInterval 15 904 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_904 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 904) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_904 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_904 : oddCount 904 15 = 3 ∧ acceleratedOrbit 15 904 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_904 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 904) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_904.1, data_15_904.2]

/-- Complete interval computation for depth 15, residue 905. -/
theorem bounds_15_905 : exactInterval 15 905 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_905 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 905) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_905 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_905 : oddCount 905 15 = 9 ∧ acceleratedOrbit 15 905 = 545 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_905 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 905) = 3 ^ 9 * m + 545 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_905.1, data_15_905.2]

/-- Complete interval computation for depth 15, residue 906. -/
theorem bounds_15_906 : exactInterval 15 906 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_906 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 906) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_906 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_906 : oddCount 906 15 = 3 ∧ acceleratedOrbit 15 906 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_906 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 906) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_906.1, data_15_906.2]

/-- Complete interval computation for depth 15, residue 907. -/
theorem bounds_15_907 : exactInterval 15 907 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_907 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 907) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_907 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_907 : oddCount 907 15 = 10 ∧ acceleratedOrbit 15 907 = 1640 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_907 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 907) = 3 ^ 10 * m + 1640 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_907.1, data_15_907.2]

/-- Complete interval computation for depth 15, residue 908. -/
theorem bounds_15_908 : exactInterval 15 908 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_908 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 908) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_908 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_908 : oddCount 908 15 = 3 ∧ acceleratedOrbit 15 908 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_908 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 908) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_908.1, data_15_908.2]

/-- Complete interval computation for depth 15, residue 909. -/
theorem bounds_15_909 : exactInterval 15 909 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_909 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 909) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_909 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_909 : oddCount 909 15 = 3 ∧ acceleratedOrbit 15 909 = 1 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_909 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 909) = 3 ^ 3 * m + 1 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_909.1, data_15_909.2]

/-- Complete interval computation for depth 15, residue 910. -/
theorem bounds_15_910 : exactInterval 15 910 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_910 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 910) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_910 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_910 : oddCount 910 15 = 7 ∧ acceleratedOrbit 15 910 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_910 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 910) = 3 ^ 7 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_910.1, data_15_910.2]

/-- Complete interval computation for depth 15, residue 911. -/
theorem bounds_15_911 : exactInterval 15 911 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_911 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 911) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_911 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_911 : oddCount 911 15 = 7 ∧ acceleratedOrbit 15 911 = 61 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_911 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 911) = 3 ^ 7 * m + 61 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_911.1, data_15_911.2]

/-- Complete interval computation for depth 15, residue 912. -/
theorem bounds_15_912 : exactInterval 15 912 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_912 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 912) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_912 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_912 : oddCount 912 15 = 5 ∧ acceleratedOrbit 15 912 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_912 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 912) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_912.1, data_15_912.2]

/-- Complete interval computation for depth 15, residue 913. -/
theorem bounds_15_913 : exactInterval 15 913 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_913 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 913) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_913 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_913 : oddCount 913 15 = 7 ∧ acceleratedOrbit 15 913 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_913 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 913) = 3 ^ 7 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_913.1, data_15_913.2]

/-- Complete interval computation for depth 15, residue 914. -/
theorem bounds_15_914 : exactInterval 15 914 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_914 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 914) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_914 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_914 : oddCount 914 15 = 7 ∧ acceleratedOrbit 15 914 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_914 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 914) = 3 ^ 7 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_914.1, data_15_914.2]

/-- Complete interval computation for depth 15, residue 915. -/
theorem bounds_15_915 : exactInterval 15 915 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_915 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 915) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_915 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_915 : oddCount 915 15 = 7 ∧ acceleratedOrbit 15 915 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_915 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 915) = 3 ^ 7 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_915.1, data_15_915.2]

/-- Complete interval computation for depth 15, residue 916. -/
theorem bounds_15_916 : exactInterval 15 916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_916 : oddCount 916 15 = 5 ∧ acceleratedOrbit 15 916 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 916) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_916.1, data_15_916.2]

end Collatz.Research.PassageAtlas.Batch0028
