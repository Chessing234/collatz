import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0487

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15925. -/
theorem bounds_15_15925 : exactInterval 15 15925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15925 : oddCount 15925 15 = 4 ∧ acceleratedOrbit 15 15925 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15925) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15925.1, data_15_15925.2]

/-- Complete interval computation for depth 15, residue 15926. -/
theorem bounds_15_15926 : exactInterval 15 15926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15926 : oddCount 15926 15 = 11 ∧ acceleratedOrbit 15 15926 = 86113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15926) = 3 ^ 11 * m + 86113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15926.1, data_15_15926.2]

/-- Complete interval computation for depth 15, residue 15927. -/
theorem bounds_15_15927 : exactInterval 15 15927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15927 : oddCount 15927 15 = 11 ∧ acceleratedOrbit 15 15927 = 86113 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15927) = 3 ^ 11 * m + 86113 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15927.1, data_15_15927.2]

/-- Complete interval computation for depth 15, residue 15928. -/
theorem bounds_15_15928 : exactInterval 15 15928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15928 : oddCount 15928 15 = 7 ∧ acceleratedOrbit 15 15928 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15928) = 3 ^ 7 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15928.1, data_15_15928.2]

/-- Complete interval computation for depth 15, residue 15929. -/
theorem bounds_15_15929 : exactInterval 15 15929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15929 : oddCount 15929 15 = 9 ∧ acceleratedOrbit 15 15929 = 9571 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15929) = 3 ^ 9 * m + 9571 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15929.1, data_15_15929.2]

/-- Complete interval computation for depth 15, residue 15930. -/
theorem bounds_15_15930 : exactInterval 15 15930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15930 : oddCount 15930 15 = 7 ∧ acceleratedOrbit 15 15930 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15930) = 3 ^ 7 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15930.1, data_15_15930.2]

/-- Complete interval computation for depth 15, residue 15931. -/
theorem bounds_15_15931 : exactInterval 15 15931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15931 : oddCount 15931 15 = 7 ∧ acceleratedOrbit 15 15931 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15931) = 3 ^ 7 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15931.1, data_15_15931.2]

/-- Complete interval computation for depth 15, residue 15932. -/
theorem bounds_15_15932 : exactInterval 15 15932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15932 : oddCount 15932 15 = 7 ∧ acceleratedOrbit 15 15932 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15932) = 3 ^ 7 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15932.1, data_15_15932.2]

/-- Complete interval computation for depth 15, residue 15933. -/
theorem bounds_15_15933 : exactInterval 15 15933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15933 : oddCount 15933 15 = 7 ∧ acceleratedOrbit 15 15933 = 1064 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15933) = 3 ^ 7 * m + 1064 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15933.1, data_15_15933.2]

/-- Complete interval computation for depth 15, residue 15934. -/
theorem bounds_15_15934 : exactInterval 15 15934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15934 : oddCount 15934 15 = 8 ∧ acceleratedOrbit 15 15934 = 3191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15934) = 3 ^ 8 * m + 3191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15934.1, data_15_15934.2]

/-- Complete interval computation for depth 15, residue 15935. -/
theorem bounds_15_15935 : exactInterval 15 15935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15935 : oddCount 15935 15 = 8 ∧ acceleratedOrbit 15 15935 = 3191 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15935) = 3 ^ 8 * m + 3191 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15935.1, data_15_15935.2]

/-- Complete interval computation for depth 15, residue 15936. -/
theorem bounds_15_15936 : exactInterval 15 15936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15936 : oddCount 15936 15 = 5 ∧ acceleratedOrbit 15 15936 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15936) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15936.1, data_15_15936.2]

/-- Complete interval computation for depth 15, residue 15937. -/
theorem bounds_15_15937 : exactInterval 15 15937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15937 : oddCount 15937 15 = 6 ∧ acceleratedOrbit 15 15937 = 355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15937) = 3 ^ 6 * m + 355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15937.1, data_15_15937.2]

/-- Complete interval computation for depth 15, residue 15938. -/
theorem bounds_15_15938 : exactInterval 15 15938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15938 : oddCount 15938 15 = 6 ∧ acceleratedOrbit 15 15938 = 355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15938) = 3 ^ 6 * m + 355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15938.1, data_15_15938.2]

/-- Complete interval computation for depth 15, residue 15939. -/
theorem bounds_15_15939 : exactInterval 15 15939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15939 : oddCount 15939 15 = 6 ∧ acceleratedOrbit 15 15939 = 355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15939) = 3 ^ 6 * m + 355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15939.1, data_15_15939.2]

/-- Complete interval computation for depth 15, residue 15940. -/
theorem bounds_15_15940 : exactInterval 15 15940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15940 : oddCount 15940 15 = 7 ∧ acceleratedOrbit 15 15940 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15940) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15940.1, data_15_15940.2]

/-- Complete interval computation for depth 15, residue 15941. -/
theorem bounds_15_15941 : exactInterval 15 15941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15941 : oddCount 15941 15 = 7 ∧ acceleratedOrbit 15 15941 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15941) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15941.1, data_15_15941.2]

/-- Complete interval computation for depth 15, residue 15942. -/
theorem bounds_15_15942 : exactInterval 15 15942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15942 : oddCount 15942 15 = 7 ∧ acceleratedOrbit 15 15942 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15942) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15942.1, data_15_15942.2]

/-- Complete interval computation for depth 15, residue 15943. -/
theorem bounds_15_15943 : exactInterval 15 15943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15943 : oddCount 15943 15 = 9 ∧ acceleratedOrbit 15 15943 = 9578 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15943) = 3 ^ 9 * m + 9578 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15943.1, data_15_15943.2]

/-- Complete interval computation for depth 15, residue 15944. -/
theorem bounds_15_15944 : exactInterval 15 15944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15944 : oddCount 15944 15 = 7 ∧ acceleratedOrbit 15 15944 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15944) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15944.1, data_15_15944.2]

/-- Complete interval computation for depth 15, residue 15945. -/
theorem bounds_15_15945 : exactInterval 15 15945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15945 : oddCount 15945 15 = 9 ∧ acceleratedOrbit 15 15945 = 9580 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15945) = 3 ^ 9 * m + 9580 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15945.1, data_15_15945.2]

/-- Complete interval computation for depth 15, residue 15946. -/
theorem bounds_15_15946 : exactInterval 15 15946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15946 : oddCount 15946 15 = 7 ∧ acceleratedOrbit 15 15946 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15946) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15946.1, data_15_15946.2]

/-- Complete interval computation for depth 15, residue 15947. -/
theorem bounds_15_15947 : exactInterval 15 15947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15947 : oddCount 15947 15 = 7 ∧ acceleratedOrbit 15 15947 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15947) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15947.1, data_15_15947.2]

/-- Complete interval computation for depth 15, residue 15948. -/
theorem bounds_15_15948 : exactInterval 15 15948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15948 : oddCount 15948 15 = 7 ∧ acceleratedOrbit 15 15948 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15948) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15948.1, data_15_15948.2]

/-- Complete interval computation for depth 15, residue 15949. -/
theorem bounds_15_15949 : exactInterval 15 15949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15949 : oddCount 15949 15 = 7 ∧ acceleratedOrbit 15 15949 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15949) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15949.1, data_15_15949.2]

/-- Complete interval computation for depth 15, residue 15950. -/
theorem bounds_15_15950 : exactInterval 15 15950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15950 : oddCount 15950 15 = 9 ∧ acceleratedOrbit 15 15950 = 9584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15950) = 3 ^ 9 * m + 9584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15950.1, data_15_15950.2]

/-- Complete interval computation for depth 15, residue 15951. -/
theorem bounds_15_15951 : exactInterval 15 15951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15951 : oddCount 15951 15 = 9 ∧ acceleratedOrbit 15 15951 = 9584 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15951) = 3 ^ 9 * m + 9584 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15951.1, data_15_15951.2]

/-- Complete interval computation for depth 15, residue 15952. -/
theorem bounds_15_15952 : exactInterval 15 15952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15952 : oddCount 15952 15 = 5 ∧ acceleratedOrbit 15 15952 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15952) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15952.1, data_15_15952.2]

/-- Complete interval computation for depth 15, residue 15953. -/
theorem bounds_15_15953 : exactInterval 15 15953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15953 : oddCount 15953 15 = 6 ∧ acceleratedOrbit 15 15953 = 355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15953) = 3 ^ 6 * m + 355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15953.1, data_15_15953.2]

/-- Complete interval computation for depth 15, residue 15954. -/
theorem bounds_15_15954 : exactInterval 15 15954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15954 : oddCount 15954 15 = 6 ∧ acceleratedOrbit 15 15954 = 355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15954) = 3 ^ 6 * m + 355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15954.1, data_15_15954.2]

/-- Complete interval computation for depth 15, residue 15955. -/
theorem bounds_15_15955 : exactInterval 15 15955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15955 : oddCount 15955 15 = 6 ∧ acceleratedOrbit 15 15955 = 355 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15955) = 3 ^ 6 * m + 355 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15955.1, data_15_15955.2]

/-- Complete interval computation for depth 15, residue 15956. -/
theorem bounds_15_15956 : exactInterval 15 15956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15956 : oddCount 15956 15 = 5 ∧ acceleratedOrbit 15 15956 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15956) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15956.1, data_15_15956.2]

/-- Complete interval computation for depth 15, residue 15957. -/
theorem bounds_15_15957 : exactInterval 15 15957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15957 : oddCount 15957 15 = 5 ∧ acceleratedOrbit 15 15957 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15957) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15957.1, data_15_15957.2]

end Collatz.Research.PassageAtlas.Batch0487
