import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0365

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11927. -/
theorem bounds_15_11927 : exactInterval 15 11927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11927 : oddCount 11927 15 = 5 ∧ acceleratedOrbit 15 11927 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11927) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11927.1, data_15_11927.2]

/-- Complete interval computation for depth 15, residue 11928. -/
theorem bounds_15_11928 : exactInterval 15 11928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11928 : oddCount 11928 15 = 8 ∧ acceleratedOrbit 15 11928 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11928) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11928.1, data_15_11928.2]

/-- Complete interval computation for depth 15, residue 11929. -/
theorem bounds_15_11929 : exactInterval 15 11929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11929 : oddCount 11929 15 = 10 ∧ acceleratedOrbit 15 11929 = 21505 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11929) = 3 ^ 10 * m + 21505 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11929.1, data_15_11929.2]

/-- Complete interval computation for depth 15, residue 11930. -/
theorem bounds_15_11930 : exactInterval 15 11930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11930 : oddCount 11930 15 = 8 ∧ acceleratedOrbit 15 11930 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11930) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11930.1, data_15_11930.2]

/-- Complete interval computation for depth 15, residue 11931. -/
theorem bounds_15_11931 : exactInterval 15 11931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11931 : oddCount 11931 15 = 10 ∧ acceleratedOrbit 15 11931 = 21503 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11931) = 3 ^ 10 * m + 21503 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11931.1, data_15_11931.2]

/-- Complete interval computation for depth 15, residue 11932. -/
theorem bounds_15_11932 : exactInterval 15 11932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11932 : oddCount 11932 15 = 9 ∧ acceleratedOrbit 15 11932 = 7172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11932) = 3 ^ 9 * m + 7172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11932.1, data_15_11932.2]

/-- Complete interval computation for depth 15, residue 11933. -/
theorem bounds_15_11933 : exactInterval 15 11933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11933 : oddCount 11933 15 = 9 ∧ acceleratedOrbit 15 11933 = 7172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11933) = 3 ^ 9 * m + 7172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11933.1, data_15_11933.2]

/-- Complete interval computation for depth 15, residue 11934. -/
theorem bounds_15_11934 : exactInterval 15 11934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11934 : oddCount 11934 15 = 9 ∧ acceleratedOrbit 15 11934 = 7172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11934) = 3 ^ 9 * m + 7172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11934.1, data_15_11934.2]

/-- Complete interval computation for depth 15, residue 11935. -/
theorem bounds_15_11935 : exactInterval 15 11935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11935 : oddCount 11935 15 = 11 ∧ acceleratedOrbit 15 11935 = 64529 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11935) = 3 ^ 11 * m + 64529 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11935.1, data_15_11935.2]

/-- Complete interval computation for depth 15, residue 11936. -/
theorem bounds_15_11936 : exactInterval 15 11936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11936 : oddCount 11936 15 = 3 ∧ acceleratedOrbit 15 11936 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11936) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11936.1, data_15_11936.2]

/-- Complete interval computation for depth 15, residue 11937. -/
theorem bounds_15_11937 : exactInterval 15 11937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11937 : oddCount 11937 15 = 7 ∧ acceleratedOrbit 15 11937 = 797 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11937) = 3 ^ 7 * m + 797 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11937.1, data_15_11937.2]

/-- Complete interval computation for depth 15, residue 11938. -/
theorem bounds_15_11938 : exactInterval 15 11938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11938 : oddCount 11938 15 = 8 ∧ acceleratedOrbit 15 11938 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11938) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11938.1, data_15_11938.2]

/-- Complete interval computation for depth 15, residue 11939. -/
theorem bounds_15_11939 : exactInterval 15 11939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11939 : oddCount 11939 15 = 8 ∧ acceleratedOrbit 15 11939 = 2393 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11939) = 3 ^ 8 * m + 2393 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11939.1, data_15_11939.2]

/-- Complete interval computation for depth 15, residue 11940. -/
theorem bounds_15_11940 : exactInterval 15 11940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11940 : oddCount 11940 15 = 8 ∧ acceleratedOrbit 15 11940 = 2392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11940) = 3 ^ 8 * m + 2392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11940.1, data_15_11940.2]

/-- Complete interval computation for depth 15, residue 11941. -/
theorem bounds_15_11941 : exactInterval 15 11941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11941 : oddCount 11941 15 = 8 ∧ acceleratedOrbit 15 11941 = 2392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11941) = 3 ^ 8 * m + 2392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11941.1, data_15_11941.2]

/-- Complete interval computation for depth 15, residue 11942. -/
theorem bounds_15_11942 : exactInterval 15 11942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11942 : oddCount 11942 15 = 8 ∧ acceleratedOrbit 15 11942 = 2392 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11942) = 3 ^ 8 * m + 2392 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11942.1, data_15_11942.2]

/-- Complete interval computation for depth 15, residue 11943. -/
theorem bounds_15_11943 : exactInterval 15 11943 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11943) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11943 : oddCount 11943 15 = 9 ∧ acceleratedOrbit 15 11943 = 7175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11943) = 3 ^ 9 * m + 7175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11943.1, data_15_11943.2]

/-- Complete interval computation for depth 15, residue 11944. -/
theorem bounds_15_11944 : exactInterval 15 11944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11944 : oddCount 11944 15 = 3 ∧ acceleratedOrbit 15 11944 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11944) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11944.1, data_15_11944.2]

/-- Complete interval computation for depth 15, residue 11945. -/
theorem bounds_15_11945 : exactInterval 15 11945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11945 : oddCount 11945 15 = 11 ∧ acceleratedOrbit 15 11945 = 64585 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11945) = 3 ^ 11 * m + 64585 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11945.1, data_15_11945.2]

/-- Complete interval computation for depth 15, residue 11946. -/
theorem bounds_15_11946 : exactInterval 15 11946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11946 : oddCount 11946 15 = 3 ∧ acceleratedOrbit 15 11946 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11946) = 3 ^ 3 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11946.1, data_15_11946.2]

/-- Complete interval computation for depth 15, residue 11947. -/
theorem bounds_15_11947 : exactInterval 15 11947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11947 : oddCount 11947 15 = 10 ∧ acceleratedOrbit 15 11947 = 21536 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11947) = 3 ^ 10 * m + 21536 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11947.1, data_15_11947.2]

/-- Complete interval computation for depth 15, residue 11948. -/
theorem bounds_15_11948 : exactInterval 15 11948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11948 : oddCount 11948 15 = 6 ∧ acceleratedOrbit 15 11948 = 266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11948) = 3 ^ 6 * m + 266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11948.1, data_15_11948.2]

/-- Complete interval computation for depth 15, residue 11949. -/
theorem bounds_15_11949 : exactInterval 15 11949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11949 : oddCount 11949 15 = 6 ∧ acceleratedOrbit 15 11949 = 266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11949) = 3 ^ 6 * m + 266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11949.1, data_15_11949.2]

/-- Complete interval computation for depth 15, residue 11950. -/
theorem bounds_15_11950 : exactInterval 15 11950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11950 : oddCount 11950 15 = 6 ∧ acceleratedOrbit 15 11950 = 266 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11950) = 3 ^ 6 * m + 266 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11950.1, data_15_11950.2]

/-- Complete interval computation for depth 15, residue 11951. -/
theorem bounds_15_11951 : exactInterval 15 11951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11951 : oddCount 11951 15 = 9 ∧ acceleratedOrbit 15 11951 = 7181 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11951) = 3 ^ 9 * m + 7181 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11951.1, data_15_11951.2]

/-- Complete interval computation for depth 15, residue 11952. -/
theorem bounds_15_11952 : exactInterval 15 11952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11952 : oddCount 11952 15 = 7 ∧ acceleratedOrbit 15 11952 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11952) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11952.1, data_15_11952.2]

/-- Complete interval computation for depth 15, residue 11953. -/
theorem bounds_15_11953 : exactInterval 15 11953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11953 : oddCount 11953 15 = 7 ∧ acceleratedOrbit 15 11953 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11953) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11953.1, data_15_11953.2]

/-- Complete interval computation for depth 15, residue 11954. -/
theorem bounds_15_11954 : exactInterval 15 11954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11954 : oddCount 11954 15 = 7 ∧ acceleratedOrbit 15 11954 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11954) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11954.1, data_15_11954.2]

/-- Complete interval computation for depth 15, residue 11955. -/
theorem bounds_15_11955 : exactInterval 15 11955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11955 : oddCount 11955 15 = 7 ∧ acceleratedOrbit 15 11955 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11955) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11955.1, data_15_11955.2]

/-- Complete interval computation for depth 15, residue 11956. -/
theorem bounds_15_11956 : exactInterval 15 11956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11956 : oddCount 11956 15 = 7 ∧ acceleratedOrbit 15 11956 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11956) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11956.1, data_15_11956.2]

/-- Complete interval computation for depth 15, residue 11957. -/
theorem bounds_15_11957 : exactInterval 15 11957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11957 : oddCount 11957 15 = 7 ∧ acceleratedOrbit 15 11957 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11957) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11957.1, data_15_11957.2]

/-- Complete interval computation for depth 15, residue 11958. -/
theorem bounds_15_11958 : exactInterval 15 11958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11958 : oddCount 11958 15 = 8 ∧ acceleratedOrbit 15 11958 = 2395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11958) = 3 ^ 8 * m + 2395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11958.1, data_15_11958.2]

/-- Complete interval computation for depth 15, residue 11959. -/
theorem bounds_15_11959 : exactInterval 15 11959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11959 : oddCount 11959 15 = 8 ∧ acceleratedOrbit 15 11959 = 2395 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11959) = 3 ^ 8 * m + 2395 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11959.1, data_15_11959.2]

end Collatz.Research.PassageAtlas.Batch0365
