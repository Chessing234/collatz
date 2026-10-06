import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0670

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 21921. -/
theorem bounds_15_21921 : exactInterval 15 21921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21921 : oddCount 21921 15 = 8 ∧ acceleratedOrbit 15 21921 = 4391 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21921) = 3 ^ 8 * m + 4391 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21921.1, data_15_21921.2]

/-- Complete interval computation for depth 15, residue 21922. -/
theorem bounds_15_21922 : exactInterval 15 21922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21922 : oddCount 21922 15 = 6 ∧ acceleratedOrbit 15 21922 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21922) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21922.1, data_15_21922.2]

/-- Complete interval computation for depth 15, residue 21923. -/
theorem bounds_15_21923 : exactInterval 15 21923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21923 : oddCount 21923 15 = 6 ∧ acceleratedOrbit 15 21923 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21923) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21923.1, data_15_21923.2]

/-- Complete interval computation for depth 15, residue 21924. -/
theorem bounds_15_21924 : exactInterval 15 21924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21924 : oddCount 21924 15 = 6 ∧ acceleratedOrbit 15 21924 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21924) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21924.1, data_15_21924.2]

/-- Complete interval computation for depth 15, residue 21925. -/
theorem bounds_15_21925 : exactInterval 15 21925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21925 : oddCount 21925 15 = 6 ∧ acceleratedOrbit 15 21925 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21925) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21925.1, data_15_21925.2]

/-- Complete interval computation for depth 15, residue 21926. -/
theorem bounds_15_21926 : exactInterval 15 21926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21926 : oddCount 21926 15 = 6 ∧ acceleratedOrbit 15 21926 = 488 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21926) = 3 ^ 6 * m + 488 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21926.1, data_15_21926.2]

/-- Complete interval computation for depth 15, residue 21927. -/
theorem bounds_15_21927 : exactInterval 15 21927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21927 : oddCount 21927 15 = 10 ∧ acceleratedOrbit 15 21927 = 39518 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21927) = 3 ^ 10 * m + 39518 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21927.1, data_15_21927.2]

/-- Complete interval computation for depth 15, residue 21928. -/
theorem bounds_15_21928 : exactInterval 15 21928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21928 : oddCount 21928 15 = 5 ∧ acceleratedOrbit 15 21928 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21928) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21928.1, data_15_21928.2]

/-- Complete interval computation for depth 15, residue 21929. -/
theorem bounds_15_21929 : exactInterval 15 21929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21929 : oddCount 21929 15 = 10 ∧ acceleratedOrbit 15 21929 = 39521 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21929) = 3 ^ 10 * m + 39521 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21929.1, data_15_21929.2]

/-- Complete interval computation for depth 15, residue 21930. -/
theorem bounds_15_21930 : exactInterval 15 21930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21930 : oddCount 21930 15 = 5 ∧ acceleratedOrbit 15 21930 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21930) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21930.1, data_15_21930.2]

/-- Complete interval computation for depth 15, residue 21931. -/
theorem bounds_15_21931 : exactInterval 15 21931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21931 : oddCount 21931 15 = 10 ∧ acceleratedOrbit 15 21931 = 39527 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21931) = 3 ^ 10 * m + 39527 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21931.1, data_15_21931.2]

/-- Complete interval computation for depth 15, residue 21932. -/
theorem bounds_15_21932 : exactInterval 15 21932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21932 : oddCount 21932 15 = 8 ∧ acceleratedOrbit 15 21932 = 4394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21932) = 3 ^ 8 * m + 4394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21932.1, data_15_21932.2]

/-- Complete interval computation for depth 15, residue 21933. -/
theorem bounds_15_21933 : exactInterval 15 21933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21933 : oddCount 21933 15 = 8 ∧ acceleratedOrbit 15 21933 = 4394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21933) = 3 ^ 8 * m + 4394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21933.1, data_15_21933.2]

/-- Complete interval computation for depth 15, residue 21934. -/
theorem bounds_15_21934 : exactInterval 15 21934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21934 : oddCount 21934 15 = 8 ∧ acceleratedOrbit 15 21934 = 4394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21934) = 3 ^ 8 * m + 4394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21934.1, data_15_21934.2]

/-- Complete interval computation for depth 15, residue 21935. -/
theorem bounds_15_21935 : exactInterval 15 21935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21935 : oddCount 21935 15 = 9 ∧ acceleratedOrbit 15 21935 = 13178 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21935) = 3 ^ 9 * m + 13178 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21935.1, data_15_21935.2]

/-- Complete interval computation for depth 15, residue 21936. -/
theorem bounds_15_21936 : exactInterval 15 21936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21936 : oddCount 21936 15 = 7 ∧ acceleratedOrbit 15 21936 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21936) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21936.1, data_15_21936.2]

/-- Complete interval computation for depth 15, residue 21937. -/
theorem bounds_15_21937 : exactInterval 15 21937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21937 : oddCount 21937 15 = 5 ∧ acceleratedOrbit 15 21937 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21937) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21937.1, data_15_21937.2]

/-- Complete interval computation for depth 15, residue 21938. -/
theorem bounds_15_21938 : exactInterval 15 21938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21938 : oddCount 21938 15 = 5 ∧ acceleratedOrbit 15 21938 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21938) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21938.1, data_15_21938.2]

/-- Complete interval computation for depth 15, residue 21939. -/
theorem bounds_15_21939 : exactInterval 15 21939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21939 : oddCount 21939 15 = 5 ∧ acceleratedOrbit 15 21939 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21939) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21939.1, data_15_21939.2]

/-- Complete interval computation for depth 15, residue 21940. -/
theorem bounds_15_21940 : exactInterval 15 21940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21940 : oddCount 21940 15 = 7 ∧ acceleratedOrbit 15 21940 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21940) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21940.1, data_15_21940.2]

/-- Complete interval computation for depth 15, residue 21941. -/
theorem bounds_15_21941 : exactInterval 15 21941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21941 : oddCount 21941 15 = 7 ∧ acceleratedOrbit 15 21941 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21941) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21941.1, data_15_21941.2]

/-- Complete interval computation for depth 15, residue 21942. -/
theorem bounds_15_21942 : exactInterval 15 21942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21942 : oddCount 21942 15 = 10 ∧ acceleratedOrbit 15 21942 = 39548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21942) = 3 ^ 10 * m + 39548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21942.1, data_15_21942.2]

/-- Complete interval computation for depth 15, residue 21943. -/
theorem bounds_15_21943 : exactInterval 15 21943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21943 : oddCount 21943 15 = 10 ∧ acceleratedOrbit 15 21943 = 39548 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21943) = 3 ^ 10 * m + 39548 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21943.1, data_15_21943.2]

/-- Complete interval computation for depth 15, residue 21944. -/
theorem bounds_15_21944 : exactInterval 15 21944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21944 : oddCount 21944 15 = 7 ∧ acceleratedOrbit 15 21944 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21944) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21944.1, data_15_21944.2]

/-- Complete interval computation for depth 15, residue 21945. -/
theorem bounds_15_21945 : exactInterval 15 21945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21945 : oddCount 21945 15 = 5 ∧ acceleratedOrbit 15 21945 = 163 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21945) = 3 ^ 5 * m + 163 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21945.1, data_15_21945.2]

/-- Complete interval computation for depth 15, residue 21946. -/
theorem bounds_15_21946 : exactInterval 15 21946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21946 : oddCount 21946 15 = 7 ∧ acceleratedOrbit 15 21946 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21946) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21946.1, data_15_21946.2]

/-- Complete interval computation for depth 15, residue 21947. -/
theorem bounds_15_21947 : exactInterval 15 21947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21947 : oddCount 21947 15 = 7 ∧ acceleratedOrbit 15 21947 = 1465 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21947) = 3 ^ 7 * m + 1465 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21947.1, data_15_21947.2]

/-- Complete interval computation for depth 15, residue 21948. -/
theorem bounds_15_21948 : exactInterval 15 21948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21948 : oddCount 21948 15 = 8 ∧ acceleratedOrbit 15 21948 = 4396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21948) = 3 ^ 8 * m + 4396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21948.1, data_15_21948.2]

/-- Complete interval computation for depth 15, residue 21949. -/
theorem bounds_15_21949 : exactInterval 15 21949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21949 : oddCount 21949 15 = 8 ∧ acceleratedOrbit 15 21949 = 4396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21949) = 3 ^ 8 * m + 4396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21949.1, data_15_21949.2]

/-- Complete interval computation for depth 15, residue 21950. -/
theorem bounds_15_21950 : exactInterval 15 21950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21950 : oddCount 21950 15 = 8 ∧ acceleratedOrbit 15 21950 = 4396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21950) = 3 ^ 8 * m + 4396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21950.1, data_15_21950.2]

/-- Complete interval computation for depth 15, residue 21951. -/
theorem bounds_15_21951 : exactInterval 15 21951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21951 : oddCount 21951 15 = 11 ∧ acceleratedOrbit 15 21951 = 118675 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21951) = 3 ^ 11 * m + 118675 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21951.1, data_15_21951.2]

/-- Complete interval computation for depth 15, residue 21952. -/
theorem bounds_15_21952 : exactInterval 15 21952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21952 : oddCount 21952 15 = 5 ∧ acceleratedOrbit 15 21952 = 164 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21952) = 3 ^ 5 * m + 164 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21952.1, data_15_21952.2]

/-- Complete interval computation for depth 15, residue 21953. -/
theorem bounds_15_21953 : exactInterval 15 21953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_21953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 21953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_21953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_21953 : oddCount 21953 15 = 7 ∧ acceleratedOrbit 15 21953 = 1466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_21953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 21953) = 3 ^ 7 * m + 1466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_21953.1, data_15_21953.2]

end Collatz.Research.PassageAtlas.Batch0670
