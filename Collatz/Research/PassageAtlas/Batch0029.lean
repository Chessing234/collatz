import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0029

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 917. -/
theorem bounds_15_917 : exactInterval 15 917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_917 : oddCount 917 15 = 5 ∧ acceleratedOrbit 15 917 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 917) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_917.1, data_15_917.2]

/-- Complete interval computation for depth 15, residue 918. -/
theorem bounds_15_918 : exactInterval 15 918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_918 : oddCount 918 15 = 8 ∧ acceleratedOrbit 15 918 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 918) = 3 ^ 8 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_918.1, data_15_918.2]

/-- Complete interval computation for depth 15, residue 919. -/
theorem bounds_15_919 : exactInterval 15 919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_919 : oddCount 919 15 = 8 ∧ acceleratedOrbit 15 919 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 919) = 3 ^ 8 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_919.1, data_15_919.2]

/-- Complete interval computation for depth 15, residue 920. -/
theorem bounds_15_920 : exactInterval 15 920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_920 : oddCount 920 15 = 5 ∧ acceleratedOrbit 15 920 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 920) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_920.1, data_15_920.2]

/-- Complete interval computation for depth 15, residue 921. -/
theorem bounds_15_921 : exactInterval 15 921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_921 : oddCount 921 15 = 8 ∧ acceleratedOrbit 15 921 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 921) = 3 ^ 8 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_921.1, data_15_921.2]

/-- Complete interval computation for depth 15, residue 922. -/
theorem bounds_15_922 : exactInterval 15 922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_922 : oddCount 922 15 = 5 ∧ acceleratedOrbit 15 922 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 922) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_922.1, data_15_922.2]

/-- Complete interval computation for depth 15, residue 923. -/
theorem bounds_15_923 : exactInterval 15 923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_923 : oddCount 923 15 = 9 ∧ acceleratedOrbit 15 923 = 557 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 923) = 3 ^ 9 * m + 557 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_923.1, data_15_923.2]

/-- Complete interval computation for depth 15, residue 924. -/
theorem bounds_15_924 : exactInterval 15 924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_924 : oddCount 924 15 = 7 ∧ acceleratedOrbit 15 924 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 924) = 3 ^ 7 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_924.1, data_15_924.2]

/-- Complete interval computation for depth 15, residue 925. -/
theorem bounds_15_925 : exactInterval 15 925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_925 : oddCount 925 15 = 7 ∧ acceleratedOrbit 15 925 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 925) = 3 ^ 7 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_925.1, data_15_925.2]

/-- Complete interval computation for depth 15, residue 926. -/
theorem bounds_15_926 : exactInterval 15 926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_926 : oddCount 926 15 = 7 ∧ acceleratedOrbit 15 926 = 62 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 926) = 3 ^ 7 * m + 62 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_926.1, data_15_926.2]

/-- Complete interval computation for depth 15, residue 927. -/
theorem bounds_15_927 : exactInterval 15 927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_927 : oddCount 927 15 = 11 ∧ acceleratedOrbit 15 927 = 5021 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 927) = 3 ^ 11 * m + 5021 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_927.1, data_15_927.2]

/-- Complete interval computation for depth 15, residue 928. -/
theorem bounds_15_928 : exactInterval 15 928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_928 : oddCount 928 15 = 5 ∧ acceleratedOrbit 15 928 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 928) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_928.1, data_15_928.2]

/-- Complete interval computation for depth 15, residue 929. -/
theorem bounds_15_929 : exactInterval 15 929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_929 : oddCount 929 15 = 8 ∧ acceleratedOrbit 15 929 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 929) = 3 ^ 8 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_929.1, data_15_929.2]

/-- Complete interval computation for depth 15, residue 930. -/
theorem bounds_15_930 : exactInterval 15 930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_930 : oddCount 930 15 = 5 ∧ acceleratedOrbit 15 930 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 930) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_930.1, data_15_930.2]

/-- Complete interval computation for depth 15, residue 931. -/
theorem bounds_15_931 : exactInterval 15 931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_931 : oddCount 931 15 = 5 ∧ acceleratedOrbit 15 931 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 931) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_931.1, data_15_931.2]

/-- Complete interval computation for depth 15, residue 932. -/
theorem bounds_15_932 : exactInterval 15 932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_932 : oddCount 932 15 = 9 ∧ acceleratedOrbit 15 932 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 932) = 3 ^ 9 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_932.1, data_15_932.2]

/-- Complete interval computation for depth 15, residue 933. -/
theorem bounds_15_933 : exactInterval 15 933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_933 : oddCount 933 15 = 9 ∧ acceleratedOrbit 15 933 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 933) = 3 ^ 9 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_933.1, data_15_933.2]

/-- Complete interval computation for depth 15, residue 934. -/
theorem bounds_15_934 : exactInterval 15 934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_934 : oddCount 934 15 = 9 ∧ acceleratedOrbit 15 934 = 566 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 934) = 3 ^ 9 * m + 566 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_934.1, data_15_934.2]

/-- Complete interval computation for depth 15, residue 935. -/
theorem bounds_15_935 : exactInterval 15 935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_935 : oddCount 935 15 = 8 ∧ acceleratedOrbit 15 935 = 188 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 935) = 3 ^ 8 * m + 188 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_935.1, data_15_935.2]

/-- Complete interval computation for depth 15, residue 936. -/
theorem bounds_15_936 : exactInterval 15 936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_936 : oddCount 936 15 = 5 ∧ acceleratedOrbit 15 936 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 936) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_936.1, data_15_936.2]

/-- Complete interval computation for depth 15, residue 937. -/
theorem bounds_15_937 : exactInterval 15 937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_937 : oddCount 937 15 = 12 ∧ acceleratedOrbit 15 937 = 15227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 937) = 3 ^ 12 * m + 15227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_937.1, data_15_937.2]

/-- Complete interval computation for depth 15, residue 938. -/
theorem bounds_15_938 : exactInterval 15 938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_938 : oddCount 938 15 = 5 ∧ acceleratedOrbit 15 938 = 8 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 938) = 3 ^ 5 * m + 8 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_938.1, data_15_938.2]

/-- Complete interval computation for depth 15, residue 939. -/
theorem bounds_15_939 : exactInterval 15 939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_939 : oddCount 939 15 = 10 ∧ acceleratedOrbit 15 939 = 1700 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 939) = 3 ^ 10 * m + 1700 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_939.1, data_15_939.2]

/-- Complete interval computation for depth 15, residue 940. -/
theorem bounds_15_940 : exactInterval 15 940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_940 : oddCount 940 15 = 8 ∧ acceleratedOrbit 15 940 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 940) = 3 ^ 8 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_940.1, data_15_940.2]

/-- Complete interval computation for depth 15, residue 941. -/
theorem bounds_15_941 : exactInterval 15 941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_941 : oddCount 941 15 = 8 ∧ acceleratedOrbit 15 941 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 941) = 3 ^ 8 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_941.1, data_15_941.2]

/-- Complete interval computation for depth 15, residue 942. -/
theorem bounds_15_942 : exactInterval 15 942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_942 : oddCount 942 15 = 8 ∧ acceleratedOrbit 15 942 = 190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 942) = 3 ^ 8 * m + 190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_942.1, data_15_942.2]

/-- Complete interval computation for depth 15, residue 943. -/
theorem bounds_15_943 : exactInterval 15 943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_943 : oddCount 943 15 = 5 ∧ acceleratedOrbit 15 943 = 7 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 943) = 3 ^ 5 * m + 7 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_943.1, data_15_943.2]

/-- Complete interval computation for depth 15, residue 944. -/
theorem bounds_15_944 : exactInterval 15 944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_944 : oddCount 944 15 = 6 ∧ acceleratedOrbit 15 944 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 944) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_944.1, data_15_944.2]

/-- Complete interval computation for depth 15, residue 945. -/
theorem bounds_15_945 : exactInterval 15 945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_945 : oddCount 945 15 = 6 ∧ acceleratedOrbit 15 945 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 945) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_945.1, data_15_945.2]

/-- Complete interval computation for depth 15, residue 946. -/
theorem bounds_15_946 : exactInterval 15 946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_946 : oddCount 946 15 = 6 ∧ acceleratedOrbit 15 946 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 946) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_946.1, data_15_946.2]

/-- Complete interval computation for depth 15, residue 947. -/
theorem bounds_15_947 : exactInterval 15 947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_947 : oddCount 947 15 = 6 ∧ acceleratedOrbit 15 947 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 947) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_947.1, data_15_947.2]

/-- Complete interval computation for depth 15, residue 948. -/
theorem bounds_15_948 : exactInterval 15 948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_948 : oddCount 948 15 = 6 ∧ acceleratedOrbit 15 948 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 948) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_948.1, data_15_948.2]

/-- Complete interval computation for depth 15, residue 949. -/
theorem bounds_15_949 : exactInterval 15 949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_949 : oddCount 949 15 = 6 ∧ acceleratedOrbit 15 949 = 22 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 949) = 3 ^ 6 * m + 22 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_949.1, data_15_949.2]

end Collatz.Research.PassageAtlas.Batch0029
