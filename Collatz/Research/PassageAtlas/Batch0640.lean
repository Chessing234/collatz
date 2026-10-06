import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0640

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 20938. -/
theorem bounds_15_20938 : exactInterval 15 20938 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20938 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20938) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20938 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20938 : oddCount 20938 15 = 7 ∧ acceleratedOrbit 15 20938 = 1399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20938 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20938) = 3 ^ 7 * m + 1399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20938.1, data_15_20938.2]

/-- Complete interval computation for depth 15, residue 20939. -/
theorem bounds_15_20939 : exactInterval 15 20939 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20939 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20939) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20939 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20939 : oddCount 20939 15 = 6 ∧ acceleratedOrbit 15 20939 = 466 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20939 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20939) = 3 ^ 6 * m + 466 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20939.1, data_15_20939.2]

/-- Complete interval computation for depth 15, residue 20940. -/
theorem bounds_15_20940 : exactInterval 15 20940 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20940 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20940) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20940 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20940 : oddCount 20940 15 = 7 ∧ acceleratedOrbit 15 20940 = 1399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20940 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20940) = 3 ^ 7 * m + 1399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20940.1, data_15_20940.2]

/-- Complete interval computation for depth 15, residue 20941. -/
theorem bounds_15_20941 : exactInterval 15 20941 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20941 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20941) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20941 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20941 : oddCount 20941 15 = 7 ∧ acceleratedOrbit 15 20941 = 1399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20941 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20941) = 3 ^ 7 * m + 1399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20941.1, data_15_20941.2]

/-- Complete interval computation for depth 15, residue 20942. -/
theorem bounds_15_20942 : exactInterval 15 20942 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20942 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20942) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20942 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20942 : oddCount 20942 15 = 10 ∧ acceleratedOrbit 15 20942 = 37745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20942 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20942) = 3 ^ 10 * m + 37745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20942.1, data_15_20942.2]

/-- Complete interval computation for depth 15, residue 20943. -/
theorem bounds_15_20943 : exactInterval 15 20943 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20943 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20943) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20943 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20943 : oddCount 20943 15 = 10 ∧ acceleratedOrbit 15 20943 = 37745 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20943 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20943) = 3 ^ 10 * m + 37745 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20943.1, data_15_20943.2]

/-- Complete interval computation for depth 15, residue 20944. -/
theorem bounds_15_20944 : exactInterval 15 20944 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20944 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20944) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20944 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20944 : oddCount 20944 15 = 7 ∧ acceleratedOrbit 15 20944 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20944 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20944) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20944.1, data_15_20944.2]

/-- Complete interval computation for depth 15, residue 20945. -/
theorem bounds_15_20945 : exactInterval 15 20945 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20945 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20945) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20945 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20945 : oddCount 20945 15 = 7 ∧ acceleratedOrbit 15 20945 = 1399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20945 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20945) = 3 ^ 7 * m + 1399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20945.1, data_15_20945.2]

/-- Complete interval computation for depth 15, residue 20946. -/
theorem bounds_15_20946 : exactInterval 15 20946 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20946 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20946) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20946 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20946 : oddCount 20946 15 = 8 ∧ acceleratedOrbit 15 20946 = 4195 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20946 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20946) = 3 ^ 8 * m + 4195 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20946.1, data_15_20946.2]

/-- Complete interval computation for depth 15, residue 20947. -/
theorem bounds_15_20947 : exactInterval 15 20947 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20947 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20947) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20947 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20947 : oddCount 20947 15 = 8 ∧ acceleratedOrbit 15 20947 = 4195 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20947 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20947) = 3 ^ 8 * m + 4195 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20947.1, data_15_20947.2]

/-- Complete interval computation for depth 15, residue 20948. -/
theorem bounds_15_20948 : exactInterval 15 20948 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20948 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20948) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20948 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20948 : oddCount 20948 15 = 7 ∧ acceleratedOrbit 15 20948 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20948 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20948) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20948.1, data_15_20948.2]

/-- Complete interval computation for depth 15, residue 20949. -/
theorem bounds_15_20949 : exactInterval 15 20949 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20949 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20949) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20949 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20949 : oddCount 20949 15 = 7 ∧ acceleratedOrbit 15 20949 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20949 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20949) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20949.1, data_15_20949.2]

/-- Complete interval computation for depth 15, residue 20950. -/
theorem bounds_15_20950 : exactInterval 15 20950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20950 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20950) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20950 : oddCount 20950 15 = 8 ∧ acceleratedOrbit 15 20950 = 4196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20950 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20950) = 3 ^ 8 * m + 4196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20950.1, data_15_20950.2]

/-- Complete interval computation for depth 15, residue 20951. -/
theorem bounds_15_20951 : exactInterval 15 20951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20951 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20951) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20951 : oddCount 20951 15 = 8 ∧ acceleratedOrbit 15 20951 = 4196 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20951 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20951) = 3 ^ 8 * m + 4196 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20951.1, data_15_20951.2]

/-- Complete interval computation for depth 15, residue 20952. -/
theorem bounds_15_20952 : exactInterval 15 20952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20952 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20952) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20952 : oddCount 20952 15 = 6 ∧ acceleratedOrbit 15 20952 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20952 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20952) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20952.1, data_15_20952.2]

/-- Complete interval computation for depth 15, residue 20953. -/
theorem bounds_15_20953 : exactInterval 15 20953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20953 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20953) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20953 : oddCount 20953 15 = 6 ∧ acceleratedOrbit 15 20953 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20953 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20953) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20953.1, data_15_20953.2]

/-- Complete interval computation for depth 15, residue 20954. -/
theorem bounds_15_20954 : exactInterval 15 20954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20954 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20954) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20954 : oddCount 20954 15 = 6 ∧ acceleratedOrbit 15 20954 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20954 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20954) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20954.1, data_15_20954.2]

/-- Complete interval computation for depth 15, residue 20955. -/
theorem bounds_15_20955 : exactInterval 15 20955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20955 : oddCount 20955 15 = 7 ∧ acceleratedOrbit 15 20955 = 1399 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20955) = 3 ^ 7 * m + 1399 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20955.1, data_15_20955.2]

/-- Complete interval computation for depth 15, residue 20956. -/
theorem bounds_15_20956 : exactInterval 15 20956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20956 : oddCount 20956 15 = 6 ∧ acceleratedOrbit 15 20956 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20956) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20956.1, data_15_20956.2]

/-- Complete interval computation for depth 15, residue 20957. -/
theorem bounds_15_20957 : exactInterval 15 20957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20957 : oddCount 20957 15 = 6 ∧ acceleratedOrbit 15 20957 = 467 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20957) = 3 ^ 6 * m + 467 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20957.1, data_15_20957.2]

/-- Complete interval computation for depth 15, residue 20958. -/
theorem bounds_15_20958 : exactInterval 15 20958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20958 : oddCount 20958 15 = 11 ∧ acceleratedOrbit 15 20958 = 113314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20958) = 3 ^ 11 * m + 113314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20958.1, data_15_20958.2]

/-- Complete interval computation for depth 15, residue 20959. -/
theorem bounds_15_20959 : exactInterval 15 20959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20959 : oddCount 20959 15 = 11 ∧ acceleratedOrbit 15 20959 = 113314 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20959) = 3 ^ 11 * m + 113314 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20959.1, data_15_20959.2]

/-- Complete interval computation for depth 15, residue 20960. -/
theorem bounds_15_20960 : exactInterval 15 20960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20960 : oddCount 20960 15 = 7 ∧ acceleratedOrbit 15 20960 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20960) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20960.1, data_15_20960.2]

/-- Complete interval computation for depth 15, residue 20961. -/
theorem bounds_15_20961 : exactInterval 15 20961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20961 : oddCount 20961 15 = 8 ∧ acceleratedOrbit 15 20961 = 4198 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20961) = 3 ^ 8 * m + 4198 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20961.1, data_15_20961.2]

/-- Complete interval computation for depth 15, residue 20962. -/
theorem bounds_15_20962 : exactInterval 15 20962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20962 : oddCount 20962 15 = 7 ∧ acceleratedOrbit 15 20962 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20962) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20962.1, data_15_20962.2]

/-- Complete interval computation for depth 15, residue 20963. -/
theorem bounds_15_20963 : exactInterval 15 20963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20963 : oddCount 20963 15 = 7 ∧ acceleratedOrbit 15 20963 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20963) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20963.1, data_15_20963.2]

/-- Complete interval computation for depth 15, residue 20964. -/
theorem bounds_15_20964 : exactInterval 15 20964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20964 : oddCount 20964 15 = 9 ∧ acceleratedOrbit 15 20964 = 12599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20964) = 3 ^ 9 * m + 12599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20964.1, data_15_20964.2]

/-- Complete interval computation for depth 15, residue 20965. -/
theorem bounds_15_20965 : exactInterval 15 20965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20965 : oddCount 20965 15 = 9 ∧ acceleratedOrbit 15 20965 = 12599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20965) = 3 ^ 9 * m + 12599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20965.1, data_15_20965.2]

/-- Complete interval computation for depth 15, residue 20966. -/
theorem bounds_15_20966 : exactInterval 15 20966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20966 : oddCount 20966 15 = 9 ∧ acceleratedOrbit 15 20966 = 12599 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20966) = 3 ^ 9 * m + 12599 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20966.1, data_15_20966.2]

/-- Complete interval computation for depth 15, residue 20967. -/
theorem bounds_15_20967 : exactInterval 15 20967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20967 : oddCount 20967 15 = 11 ∧ acceleratedOrbit 15 20967 = 113359 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20967) = 3 ^ 11 * m + 113359 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20967.1, data_15_20967.2]

/-- Complete interval computation for depth 15, residue 20968. -/
theorem bounds_15_20968 : exactInterval 15 20968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20968 : oddCount 20968 15 = 7 ∧ acceleratedOrbit 15 20968 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20968) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20968.1, data_15_20968.2]

/-- Complete interval computation for depth 15, residue 20969. -/
theorem bounds_15_20969 : exactInterval 15 20969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20969 : oddCount 20969 15 = 8 ∧ acceleratedOrbit 15 20969 = 4199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20969) = 3 ^ 8 * m + 4199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20969.1, data_15_20969.2]

/-- Complete interval computation for depth 15, residue 20970. -/
theorem bounds_15_20970 : exactInterval 15 20970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_20970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 20970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_20970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_20970 : oddCount 20970 15 = 7 ∧ acceleratedOrbit 15 20970 = 1403 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_20970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 20970) = 3 ^ 7 * m + 1403 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_20970.1, data_15_20970.2]

end Collatz.Research.PassageAtlas.Batch0640
