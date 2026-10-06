import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0263

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 952. -/
theorem bounds_12_952 : exactInterval 12 952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_952 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 952) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_952 : oddCount 952 12 = 4 ∧ acceleratedOrbit 12 952 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_952 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 952) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_952.1, data_12_952.2]

/-- Complete interval computation for depth 12, residue 953. -/
theorem bounds_12_953 : exactInterval 12 953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_953 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 953) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_953 : oddCount 953 12 = 7 ∧ acceleratedOrbit 12 953 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_953 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 953) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_953.1, data_12_953.2]

/-- Complete interval computation for depth 12, residue 954. -/
theorem bounds_12_954 : exactInterval 12 954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_954 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 954) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_954 : oddCount 954 12 = 4 ∧ acceleratedOrbit 12 954 = 19 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_954 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 954) = 3 ^ 4 * m + 19 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_954.1, data_12_954.2]

/-- Complete interval computation for depth 12, residue 955. -/
theorem bounds_12_955 : exactInterval 12 955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_955 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 955) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_955 : oddCount 955 12 = 7 ∧ acceleratedOrbit 12 955 = 512 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_955 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 955) = 3 ^ 7 * m + 512 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_955.1, data_12_955.2]

/-- Complete interval computation for depth 12, residue 956. -/
theorem bounds_12_956 : exactInterval 12 956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_956 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 956) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_956 : oddCount 956 12 = 9 ∧ acceleratedOrbit 12 956 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_956 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 956) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_956.1, data_12_956.2]

/-- Complete interval computation for depth 12, residue 957. -/
theorem bounds_12_957 : exactInterval 12 957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_957 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 957) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_957 : oddCount 957 12 = 9 ∧ acceleratedOrbit 12 957 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_957 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 957) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_957.1, data_12_957.2]

/-- Complete interval computation for depth 12, residue 958. -/
theorem bounds_12_958 : exactInterval 12 958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_958 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 958) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_958 : oddCount 958 12 = 9 ∧ acceleratedOrbit 12 958 = 4616 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_958 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 958) = 3 ^ 9 * m + 4616 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_958.1, data_12_958.2]

/-- Complete interval computation for depth 12, residue 959. -/
theorem bounds_12_959 : exactInterval 12 959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_959 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 959) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_959 : oddCount 959 12 = 10 ∧ acceleratedOrbit 12 959 = 13841 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_959 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 959) = 3 ^ 10 * m + 13841 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_959.1, data_12_959.2]

/-- Complete interval computation for depth 12, residue 960. -/
theorem bounds_12_960 : exactInterval 12 960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_960 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 960) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_960 : oddCount 960 12 = 4 ∧ acceleratedOrbit 12 960 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_960 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 960) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_960.1, data_12_960.2]

/-- Complete interval computation for depth 12, residue 961. -/
theorem bounds_12_961 : exactInterval 12 961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_961 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 961) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_961 : oddCount 961 12 = 6 ∧ acceleratedOrbit 12 961 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_961 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 961) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_961.1, data_12_961.2]

/-- Complete interval computation for depth 12, residue 962. -/
theorem bounds_12_962 : exactInterval 12 962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_962 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 962) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_962 : oddCount 962 12 = 6 ∧ acceleratedOrbit 12 962 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_962 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 962) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_962.1, data_12_962.2]

/-- Complete interval computation for depth 12, residue 963. -/
theorem bounds_12_963 : exactInterval 12 963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_963 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 963) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_963 : oddCount 963 12 = 6 ∧ acceleratedOrbit 12 963 = 172 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_963 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 963) = 3 ^ 6 * m + 172 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_963.1, data_12_963.2]

/-- Complete interval computation for depth 12, residue 964. -/
theorem bounds_12_964 : exactInterval 12 964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_964 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 964) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_964 : oddCount 964 12 = 4 ∧ acceleratedOrbit 12 964 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_964 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 964) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_964.1, data_12_964.2]

/-- Complete interval computation for depth 12, residue 965. -/
theorem bounds_12_965 : exactInterval 12 965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_965 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 965) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_965 : oddCount 965 12 = 4 ∧ acceleratedOrbit 12 965 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_965 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 965) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_965.1, data_12_965.2]

/-- Complete interval computation for depth 12, residue 966. -/
theorem bounds_12_966 : exactInterval 12 966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_966 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 966) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_966 : oddCount 966 12 = 4 ∧ acceleratedOrbit 12 966 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_966 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 966) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_966.1, data_12_966.2]

end Collatz.Research.StoppingAtlas.Batch0263
