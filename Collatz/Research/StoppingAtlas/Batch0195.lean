import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0195

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 11, residue 1955. -/
theorem bounds_11_1955 : exactInterval 11 1955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1955 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1955) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1955 : oddCount 1955 11 = 5 ∧ acceleratedOrbit 11 1955 = 233 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1955 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1955) = 3 ^ 5 * m + 233 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1955.1, data_11_1955.2]

/-- Complete interval computation for depth 11, residue 1956. -/
theorem bounds_11_1956 : exactInterval 11 1956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1956 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1956) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1956 : oddCount 1956 11 = 7 ∧ acceleratedOrbit 11 1956 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1956 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1956) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1956.1, data_11_1956.2]

/-- Complete interval computation for depth 11, residue 1957. -/
theorem bounds_11_1957 : exactInterval 11 1957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1957 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1957) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1957 : oddCount 1957 11 = 7 ∧ acceleratedOrbit 11 1957 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1957 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1957) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1957.1, data_11_1957.2]

/-- Complete interval computation for depth 11, residue 1958. -/
theorem bounds_11_1958 : exactInterval 11 1958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1958 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1958) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1958 : oddCount 1958 11 = 7 ∧ acceleratedOrbit 11 1958 = 2096 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1958 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1958) = 3 ^ 7 * m + 2096 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1958.1, data_11_1958.2]

/-- Complete interval computation for depth 11, residue 1959. -/
theorem bounds_11_1959 : exactInterval 11 1959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1959 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1959) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1959 : oddCount 1959 11 = 8 ∧ acceleratedOrbit 11 1959 = 6281 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1959 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1959) = 3 ^ 8 * m + 6281 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1959.1, data_11_1959.2]

/-- Complete interval computation for depth 11, residue 1960. -/
theorem bounds_11_1960 : exactInterval 11 1960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1960 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1960) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1960 : oddCount 1960 11 = 4 ∧ acceleratedOrbit 11 1960 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1960 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1960) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1960.1, data_11_1960.2]

/-- Complete interval computation for depth 11, residue 1961. -/
theorem bounds_11_1961 : exactInterval 11 1961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1961 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1961) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1961 : oddCount 1961 11 = 9 ∧ acceleratedOrbit 11 1961 = 18863 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1961 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1961) = 3 ^ 9 * m + 18863 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1961.1, data_11_1961.2]

/-- Complete interval computation for depth 11, residue 1962. -/
theorem bounds_11_1962 : exactInterval 11 1962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1962 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1962) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1962 : oddCount 1962 11 = 4 ∧ acceleratedOrbit 11 1962 = 80 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1962 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1962) = 3 ^ 4 * m + 80 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1962.1, data_11_1962.2]

/-- Complete interval computation for depth 11, residue 1963. -/
theorem bounds_11_1963 : exactInterval 11 1963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1963 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1963) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1963 : oddCount 1963 11 = 7 ∧ acceleratedOrbit 11 1963 = 2099 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1963 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1963) = 3 ^ 7 * m + 2099 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1963.1, data_11_1963.2]

/-- Complete interval computation for depth 11, residue 1964. -/
theorem bounds_11_1964 : exactInterval 11 1964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1964 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1964) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1964 : oddCount 1964 11 = 7 ∧ acceleratedOrbit 11 1964 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1964 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1964) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1964.1, data_11_1964.2]

/-- Complete interval computation for depth 11, residue 1965. -/
theorem bounds_11_1965 : exactInterval 11 1965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1965 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1965) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1965 : oddCount 1965 11 = 7 ∧ acceleratedOrbit 11 1965 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1965 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1965) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1965.1, data_11_1965.2]

/-- Complete interval computation for depth 11, residue 1966. -/
theorem bounds_11_1966 : exactInterval 11 1966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1966 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1966) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1966 : oddCount 1966 11 = 7 ∧ acceleratedOrbit 11 1966 = 2105 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1966 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1966) = 3 ^ 7 * m + 2105 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1966.1, data_11_1966.2]

/-- Complete interval computation for depth 11, residue 1967. -/
theorem bounds_11_1967 : exactInterval 11 1967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1967 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1967) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1967 : oddCount 1967 11 = 6 ∧ acceleratedOrbit 11 1967 = 701 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1967 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1967) = 3 ^ 6 * m + 701 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1967.1, data_11_1967.2]

/-- Complete interval computation for depth 11, residue 1968. -/
theorem bounds_11_1968 : exactInterval 11 1968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1968 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1968) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1968 : oddCount 1968 11 = 5 ∧ acceleratedOrbit 11 1968 = 236 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1968 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1968) = 3 ^ 5 * m + 236 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1968.1, data_11_1968.2]

/-- Complete interval computation for depth 11, residue 1969. -/
theorem bounds_11_1969 : exactInterval 11 1969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1969 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1969) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1969 : oddCount 1969 11 = 3 ∧ acceleratedOrbit 11 1969 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1969 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1969) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1969.1, data_11_1969.2]

/-- Complete interval computation for depth 11, residue 1970. -/
theorem bounds_11_1970 : exactInterval 11 1970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_11_1970 (m : Nat) :
    stoppingTime (2 ^ 11 * m + 1970) 11 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_11_1970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_11_1970 : oddCount 1970 11 = 3 ∧ acceleratedOrbit 11 1970 = 26 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_11_1970 (m : Nat) :
    acceleratedOrbit 11 (2 ^ 11 * m + 1970) = 3 ^ 3 * m + 26 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_11_1970.1, data_11_1970.2]

end Collatz.Research.StoppingAtlas.Batch0195
