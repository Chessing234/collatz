import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0975

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 31916. -/
theorem bounds_15_31916 : exactInterval 15 31916 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31916 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31916) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31916 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31916 : oddCount 31916 15 = 7 ∧ acceleratedOrbit 15 31916 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31916 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31916) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31916.1, data_15_31916.2]

/-- Complete interval computation for depth 15, residue 31917. -/
theorem bounds_15_31917 : exactInterval 15 31917 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31917 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31917) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31917 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31917 : oddCount 31917 15 = 7 ∧ acceleratedOrbit 15 31917 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31917 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31917) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31917.1, data_15_31917.2]

/-- Complete interval computation for depth 15, residue 31918. -/
theorem bounds_15_31918 : exactInterval 15 31918 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31918 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31918) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31918 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31918 : oddCount 31918 15 = 7 ∧ acceleratedOrbit 15 31918 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31918 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31918) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31918.1, data_15_31918.2]

/-- Complete interval computation for depth 15, residue 31919. -/
theorem bounds_15_31919 : exactInterval 15 31919 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31919 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31919) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31919 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31919 : oddCount 31919 15 = 10 ∧ acceleratedOrbit 15 31919 = 57523 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31919 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31919) = 3 ^ 10 * m + 57523 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31919.1, data_15_31919.2]

/-- Complete interval computation for depth 15, residue 31920. -/
theorem bounds_15_31920 : exactInterval 15 31920 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31920 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31920) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31920 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31920 : oddCount 31920 15 = 4 ∧ acceleratedOrbit 15 31920 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31920 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31920) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31920.1, data_15_31920.2]

/-- Complete interval computation for depth 15, residue 31921. -/
theorem bounds_15_31921 : exactInterval 15 31921 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31921 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31921) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31921 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31921 : oddCount 31921 15 = 8 ∧ acceleratedOrbit 15 31921 = 6394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31921 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31921) = 3 ^ 8 * m + 6394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31921.1, data_15_31921.2]

/-- Complete interval computation for depth 15, residue 31922. -/
theorem bounds_15_31922 : exactInterval 15 31922 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31922 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31922) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31922 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31922 : oddCount 31922 15 = 8 ∧ acceleratedOrbit 15 31922 = 6394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31922 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31922) = 3 ^ 8 * m + 6394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31922.1, data_15_31922.2]

/-- Complete interval computation for depth 15, residue 31923. -/
theorem bounds_15_31923 : exactInterval 15 31923 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31923 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31923) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31923 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31923 : oddCount 31923 15 = 8 ∧ acceleratedOrbit 15 31923 = 6394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31923 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31923) = 3 ^ 8 * m + 6394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31923.1, data_15_31923.2]

/-- Complete interval computation for depth 15, residue 31924. -/
theorem bounds_15_31924 : exactInterval 15 31924 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31924 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31924) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31924 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31924 : oddCount 31924 15 = 4 ∧ acceleratedOrbit 15 31924 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31924 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31924) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31924.1, data_15_31924.2]

/-- Complete interval computation for depth 15, residue 31925. -/
theorem bounds_15_31925 : exactInterval 15 31925 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31925 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31925) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31925 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31925 : oddCount 31925 15 = 4 ∧ acceleratedOrbit 15 31925 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31925 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31925) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31925.1, data_15_31925.2]

/-- Complete interval computation for depth 15, residue 31926. -/
theorem bounds_15_31926 : exactInterval 15 31926 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31926 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31926) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31926 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31926 : oddCount 31926 15 = 7 ∧ acceleratedOrbit 15 31926 = 2131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31926 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31926) = 3 ^ 7 * m + 2131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31926.1, data_15_31926.2]

/-- Complete interval computation for depth 15, residue 31927. -/
theorem bounds_15_31927 : exactInterval 15 31927 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31927 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31927) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31927 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31927 : oddCount 31927 15 = 7 ∧ acceleratedOrbit 15 31927 = 2131 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31927 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31927) = 3 ^ 7 * m + 2131 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31927.1, data_15_31927.2]

/-- Complete interval computation for depth 15, residue 31928. -/
theorem bounds_15_31928 : exactInterval 15 31928 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31928 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31928) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31928 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31928 : oddCount 31928 15 = 4 ∧ acceleratedOrbit 15 31928 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31928 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31928) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31928.1, data_15_31928.2]

/-- Complete interval computation for depth 15, residue 31929. -/
theorem bounds_15_31929 : exactInterval 15 31929 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31929 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31929) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31929 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31929 : oddCount 31929 15 = 8 ∧ acceleratedOrbit 15 31929 = 6394 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31929 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31929) = 3 ^ 8 * m + 6394 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31929.1, data_15_31929.2]

/-- Complete interval computation for depth 15, residue 31930. -/
theorem bounds_15_31930 : exactInterval 15 31930 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31930 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31930) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31930 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31930 : oddCount 31930 15 = 4 ∧ acceleratedOrbit 15 31930 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31930 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31930) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31930.1, data_15_31930.2]

/-- Complete interval computation for depth 15, residue 31931. -/
theorem bounds_15_31931 : exactInterval 15 31931 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31931 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31931) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31931 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31931 : oddCount 31931 15 = 11 ∧ acceleratedOrbit 15 31931 = 172637 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31931 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31931) = 3 ^ 11 * m + 172637 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31931.1, data_15_31931.2]

/-- Complete interval computation for depth 15, residue 31932. -/
theorem bounds_15_31932 : exactInterval 15 31932 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31932 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31932) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31932 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31932 : oddCount 31932 15 = 7 ∧ acceleratedOrbit 15 31932 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31932 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31932) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31932.1, data_15_31932.2]

/-- Complete interval computation for depth 15, residue 31933. -/
theorem bounds_15_31933 : exactInterval 15 31933 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31933 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31933) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31933 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31933 : oddCount 31933 15 = 7 ∧ acceleratedOrbit 15 31933 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31933 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31933) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31933.1, data_15_31933.2]

/-- Complete interval computation for depth 15, residue 31934. -/
theorem bounds_15_31934 : exactInterval 15 31934 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31934 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31934) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31934 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31934 : oddCount 31934 15 = 7 ∧ acceleratedOrbit 15 31934 = 2132 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31934 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31934) = 3 ^ 7 * m + 2132 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31934.1, data_15_31934.2]

/-- Complete interval computation for depth 15, residue 31935. -/
theorem bounds_15_31935 : exactInterval 15 31935 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31935 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31935) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31935 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31935 : oddCount 31935 15 = 11 ∧ acceleratedOrbit 15 31935 = 172651 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31935 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31935) = 3 ^ 11 * m + 172651 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31935.1, data_15_31935.2]

/-- Complete interval computation for depth 15, residue 31936. -/
theorem bounds_15_31936 : exactInterval 15 31936 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31936 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31936) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31936 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31936 : oddCount 31936 15 = 5 ∧ acceleratedOrbit 15 31936 = 238 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31936 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31936) = 3 ^ 5 * m + 238 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31936.1, data_15_31936.2]

/-- Complete interval computation for depth 15, residue 31937. -/
theorem bounds_15_31937 : exactInterval 15 31937 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31937 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31937) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31937 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31937 : oddCount 31937 15 = 8 ∧ acceleratedOrbit 15 31937 = 6398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31937 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31937) = 3 ^ 8 * m + 6398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31937.1, data_15_31937.2]

/-- Complete interval computation for depth 15, residue 31938. -/
theorem bounds_15_31938 : exactInterval 15 31938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31938 : oddCount 31938 15 = 8 ∧ acceleratedOrbit 15 31938 = 6398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31938) = 3 ^ 8 * m + 6398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31938.1, data_15_31938.2]

/-- Complete interval computation for depth 15, residue 31939. -/
theorem bounds_15_31939 : exactInterval 15 31939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31939 : oddCount 31939 15 = 8 ∧ acceleratedOrbit 15 31939 = 6398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31939) = 3 ^ 8 * m + 6398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31939.1, data_15_31939.2]

/-- Complete interval computation for depth 15, residue 31940. -/
theorem bounds_15_31940 : exactInterval 15 31940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31940 : oddCount 31940 15 = 4 ∧ acceleratedOrbit 15 31940 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31940) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31940.1, data_15_31940.2]

/-- Complete interval computation for depth 15, residue 31941. -/
theorem bounds_15_31941 : exactInterval 15 31941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31941 : oddCount 31941 15 = 4 ∧ acceleratedOrbit 15 31941 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31941) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31941.1, data_15_31941.2]

/-- Complete interval computation for depth 15, residue 31942. -/
theorem bounds_15_31942 : exactInterval 15 31942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31942 : oddCount 31942 15 = 4 ∧ acceleratedOrbit 15 31942 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31942) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31942.1, data_15_31942.2]

/-- Complete interval computation for depth 15, residue 31943. -/
theorem bounds_15_31943 : exactInterval 15 31943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31943 : oddCount 31943 15 = 9 ∧ acceleratedOrbit 15 31943 = 19190 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31943) = 3 ^ 9 * m + 19190 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31943.1, data_15_31943.2]

/-- Complete interval computation for depth 15, residue 31944. -/
theorem bounds_15_31944 : exactInterval 15 31944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31944 : oddCount 31944 15 = 4 ∧ acceleratedOrbit 15 31944 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31944) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31944.1, data_15_31944.2]

/-- Complete interval computation for depth 15, residue 31945. -/
theorem bounds_15_31945 : exactInterval 15 31945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31945 : oddCount 31945 15 = 9 ∧ acceleratedOrbit 15 31945 = 19196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31945) = 3 ^ 9 * m + 19196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31945.1, data_15_31945.2]

/-- Complete interval computation for depth 15, residue 31946. -/
theorem bounds_15_31946 : exactInterval 15 31946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31946 : oddCount 31946 15 = 4 ∧ acceleratedOrbit 15 31946 = 79 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31946) = 3 ^ 4 * m + 79 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31946.1, data_15_31946.2]

/-- Complete interval computation for depth 15, residue 31947. -/
theorem bounds_15_31947 : exactInterval 15 31947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_31947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 31947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_31947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_31947 : oddCount 31947 15 = 9 ∧ acceleratedOrbit 15 31947 = 19196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_31947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 31947) = 3 ^ 9 * m + 19196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_31947.1, data_15_31947.2]

end Collatz.Research.PassageAtlas.Batch0975
