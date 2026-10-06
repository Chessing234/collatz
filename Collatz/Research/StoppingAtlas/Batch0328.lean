import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0328

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 12, residue 1950. -/
theorem bounds_12_1950 : exactInterval 12 1950 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1950 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1950) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1950 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1950 : oddCount 1950 12 = 7 ∧ acceleratedOrbit 12 1950 = 1043 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1950 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1950) = 3 ^ 7 * m + 1043 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1950.1, data_12_1950.2]

/-- Complete interval computation for depth 12, residue 1951. -/
theorem bounds_12_1951 : exactInterval 12 1951 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1951 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1951) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1951 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1951 : oddCount 1951 12 = 8 ∧ acceleratedOrbit 12 1951 = 3127 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1951 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1951) = 3 ^ 8 * m + 3127 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1951.1, data_12_1951.2]

/-- Complete interval computation for depth 12, residue 1952. -/
theorem bounds_12_1952 : exactInterval 12 1952 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1952 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1952) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1952 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1952 : oddCount 1952 12 = 4 ∧ acceleratedOrbit 12 1952 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1952 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1952) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1952.1, data_12_1952.2]

/-- Complete interval computation for depth 12, residue 1953. -/
theorem bounds_12_1953 : exactInterval 12 1953 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1953 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1953) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1953 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1953 : oddCount 1953 12 = 5 ∧ acceleratedOrbit 12 1953 = 116 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1953 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1953) = 3 ^ 5 * m + 116 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1953.1, data_12_1953.2]

/-- Complete interval computation for depth 12, residue 1954. -/
theorem bounds_12_1954 : exactInterval 12 1954 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1954 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1954) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1954 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1954 : oddCount 1954 12 = 6 ∧ acceleratedOrbit 12 1954 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1954 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1954) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1954.1, data_12_1954.2]

/-- Complete interval computation for depth 12, residue 1955. -/
theorem bounds_12_1955 : exactInterval 12 1955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1955 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1955) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1955 : oddCount 1955 12 = 6 ∧ acceleratedOrbit 12 1955 = 350 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1955 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1955) = 3 ^ 6 * m + 350 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1955.1, data_12_1955.2]

/-- Complete interval computation for depth 12, residue 1956. -/
theorem bounds_12_1956 : exactInterval 12 1956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1956 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1956) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1956 : oddCount 1956 12 = 7 ∧ acceleratedOrbit 12 1956 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1956 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1956) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1956.1, data_12_1956.2]

/-- Complete interval computation for depth 12, residue 1957. -/
theorem bounds_12_1957 : exactInterval 12 1957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1957 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1957) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1957 : oddCount 1957 12 = 7 ∧ acceleratedOrbit 12 1957 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1957 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1957) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1957.1, data_12_1957.2]

/-- Complete interval computation for depth 12, residue 1958. -/
theorem bounds_12_1958 : exactInterval 12 1958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1958 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1958) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1958 : oddCount 1958 12 = 7 ∧ acceleratedOrbit 12 1958 = 1048 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1958 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1958) = 3 ^ 7 * m + 1048 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1958.1, data_12_1958.2]

/-- Complete interval computation for depth 12, residue 1959. -/
theorem bounds_12_1959 : exactInterval 12 1959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1959 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1959) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1959 : oddCount 1959 12 = 9 ∧ acceleratedOrbit 12 1959 = 9422 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1959 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1959) = 3 ^ 9 * m + 9422 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1959.1, data_12_1959.2]

/-- Complete interval computation for depth 12, residue 1960. -/
theorem bounds_12_1960 : exactInterval 12 1960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1960 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1960) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1960 : oddCount 1960 12 = 4 ∧ acceleratedOrbit 12 1960 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1960 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1960) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1960.1, data_12_1960.2]

/-- Complete interval computation for depth 12, residue 1961. -/
theorem bounds_12_1961 : exactInterval 12 1961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1961 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1961) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1961 : oddCount 1961 12 = 10 ∧ acceleratedOrbit 12 1961 = 28295 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1961 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1961) = 3 ^ 10 * m + 28295 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1961.1, data_12_1961.2]

/-- Complete interval computation for depth 12, residue 1962. -/
theorem bounds_12_1962 : exactInterval 12 1962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1962 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1962) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1962 : oddCount 1962 12 = 4 ∧ acceleratedOrbit 12 1962 = 40 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1962 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1962) = 3 ^ 4 * m + 40 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1962.1, data_12_1962.2]

/-- Complete interval computation for depth 12, residue 1963. -/
theorem bounds_12_1963 : exactInterval 12 1963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1963 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1963) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1963 : oddCount 1963 12 = 8 ∧ acceleratedOrbit 12 1963 = 3149 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1963 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1963) = 3 ^ 8 * m + 3149 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1963.1, data_12_1963.2]

/-- Complete interval computation for depth 12, residue 1964. -/
theorem bounds_12_1964 : exactInterval 12 1964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1964 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1964) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1964 : oddCount 1964 12 = 8 ∧ acceleratedOrbit 12 1964 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1964 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1964) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1964.1, data_12_1964.2]

/-- Complete interval computation for depth 12, residue 1965. -/
theorem bounds_12_1965 : exactInterval 12 1965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_12_1965 (m : Nat) :
    stoppingTime (2 ^ 12 * m + 1965) 12 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_12_1965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_12_1965 : oddCount 1965 12 = 8 ∧ acceleratedOrbit 12 1965 = 3158 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_12_1965 (m : Nat) :
    acceleratedOrbit 12 (2 ^ 12 * m + 1965) = 3 ^ 8 * m + 3158 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_12_1965.1, data_12_1965.2]

end Collatz.Research.StoppingAtlas.Batch0328
