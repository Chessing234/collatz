import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0063

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 10, residue 952. -/
theorem bounds_10_952 : exactInterval 10 952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_952 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 952) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_952 : oddCount 952 10 = 4 ∧ acceleratedOrbit 10 952 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_952 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 952) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_952.1, data_10_952.2]

/-- Complete interval computation for depth 10, residue 953. -/
theorem bounds_10_953 : exactInterval 10 953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_953 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 953) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_953 : oddCount 953 10 = 5 ∧ acceleratedOrbit 10 953 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_953 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 953) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_953.1, data_10_953.2]

/-- Complete interval computation for depth 10, residue 954. -/
theorem bounds_10_954 : exactInterval 10 954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_954 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 954) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_954 : oddCount 954 10 = 4 ∧ acceleratedOrbit 10 954 = 76 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_954 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 954) = 3 ^ 4 * m + 76 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_954.1, data_10_954.2]

/-- Complete interval computation for depth 10, residue 955. -/
theorem bounds_10_955 : exactInterval 10 955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_955 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 955) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_955 : oddCount 955 10 = 5 ∧ acceleratedOrbit 10 955 = 227 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_955 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 955) = 3 ^ 5 * m + 227 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_955.1, data_10_955.2]

/-- Complete interval computation for depth 10, residue 956. -/
theorem bounds_10_956 : exactInterval 10 956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_956 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 956) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_956 : oddCount 956 10 = 7 ∧ acceleratedOrbit 10 956 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_956 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 956) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_956.1, data_10_956.2]

/-- Complete interval computation for depth 10, residue 957. -/
theorem bounds_10_957 : exactInterval 10 957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_957 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 957) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_957 : oddCount 957 10 = 7 ∧ acceleratedOrbit 10 957 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_957 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 957) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_957.1, data_10_957.2]

/-- Complete interval computation for depth 10, residue 958. -/
theorem bounds_10_958 : exactInterval 10 958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_958 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 958) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_958 : oddCount 958 10 = 7 ∧ acceleratedOrbit 10 958 = 2051 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_958 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 958) = 3 ^ 7 * m + 2051 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_958.1, data_10_958.2]

/-- Complete interval computation for depth 10, residue 959. -/
theorem bounds_10_959 : exactInterval 10 959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_959 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 959) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_959 : oddCount 959 10 = 8 ∧ acceleratedOrbit 10 959 = 6151 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_959 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 959) = 3 ^ 8 * m + 6151 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_959.1, data_10_959.2]

/-- Complete interval computation for depth 10, residue 960. -/
theorem bounds_10_960 : exactInterval 10 960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_960 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 960) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_960 : oddCount 960 10 = 4 ∧ acceleratedOrbit 10 960 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_960 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 960) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_960.1, data_10_960.2]

/-- Complete interval computation for depth 10, residue 961. -/
theorem bounds_10_961 : exactInterval 10 961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_961 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 961) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_961 : oddCount 961 10 = 5 ∧ acceleratedOrbit 10 961 = 229 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_961 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 961) = 3 ^ 5 * m + 229 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_961.1, data_10_961.2]

/-- Complete interval computation for depth 10, residue 962. -/
theorem bounds_10_962 : exactInterval 10 962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_962 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 962) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_962 : oddCount 962 10 = 6 ∧ acceleratedOrbit 10 962 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_962 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 962) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_962.1, data_10_962.2]

/-- Complete interval computation for depth 10, residue 963. -/
theorem bounds_10_963 : exactInterval 10 963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_963 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 963) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_963 : oddCount 963 10 = 6 ∧ acceleratedOrbit 10 963 = 688 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_963 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 963) = 3 ^ 6 * m + 688 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_963.1, data_10_963.2]

/-- Complete interval computation for depth 10, residue 964. -/
theorem bounds_10_964 : exactInterval 10 964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_964 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 964) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_964 : oddCount 964 10 = 3 ∧ acceleratedOrbit 10 964 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_964 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 964) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_964.1, data_10_964.2]

/-- Complete interval computation for depth 10, residue 965. -/
theorem bounds_10_965 : exactInterval 10 965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_965 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 965) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_965 : oddCount 965 10 = 3 ∧ acceleratedOrbit 10 965 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_965 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 965) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_965.1, data_10_965.2]

/-- Complete interval computation for depth 10, residue 966. -/
theorem bounds_10_966 : exactInterval 10 966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_10_966 (m : Nat) :
    stoppingTime (2 ^ 10 * m + 966) 10 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_10_966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_10_966 : oddCount 966 10 = 3 ∧ acceleratedOrbit 10 966 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_10_966 (m : Nat) :
    acceleratedOrbit 10 (2 ^ 10 * m + 966) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_10_966.1, data_10_966.2]

end Collatz.Research.StoppingAtlas.Batch0063
