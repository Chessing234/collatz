import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0595

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 1955. -/
theorem bounds_13_1955 : exactInterval 13 1955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1955 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1955) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1955 : oddCount 1955 13 = 6 ∧ acceleratedOrbit 13 1955 = 175 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1955 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1955) = 3 ^ 6 * m + 175 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1955.1, data_13_1955.2]

/-- Complete interval computation for depth 13, residue 1956. -/
theorem bounds_13_1956 : exactInterval 13 1956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1956 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1956) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1956 : oddCount 1956 13 = 7 ∧ acceleratedOrbit 13 1956 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1956 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1956) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1956.1, data_13_1956.2]

/-- Complete interval computation for depth 13, residue 1957. -/
theorem bounds_13_1957 : exactInterval 13 1957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1957 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1957) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1957 : oddCount 1957 13 = 7 ∧ acceleratedOrbit 13 1957 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1957 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1957) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1957.1, data_13_1957.2]

/-- Complete interval computation for depth 13, residue 1958. -/
theorem bounds_13_1958 : exactInterval 13 1958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1958 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1958) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1958 : oddCount 1958 13 = 7 ∧ acceleratedOrbit 13 1958 = 524 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1958 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1958) = 3 ^ 7 * m + 524 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1958.1, data_13_1958.2]

/-- Complete interval computation for depth 13, residue 1959. -/
theorem bounds_13_1959 : exactInterval 13 1959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1959 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1959) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1959 : oddCount 1959 13 = 9 ∧ acceleratedOrbit 13 1959 = 4711 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1959 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1959) = 3 ^ 9 * m + 4711 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1959.1, data_13_1959.2]

/-- Complete interval computation for depth 13, residue 1960. -/
theorem bounds_13_1960 : exactInterval 13 1960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1960 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1960) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1960 : oddCount 1960 13 = 4 ∧ acceleratedOrbit 13 1960 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1960 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1960) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1960.1, data_13_1960.2]

/-- Complete interval computation for depth 13, residue 1961. -/
theorem bounds_13_1961 : exactInterval 13 1961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1961 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1961) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1961 : oddCount 1961 13 = 11 ∧ acceleratedOrbit 13 1961 = 42443 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1961 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1961) = 3 ^ 11 * m + 42443 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1961.1, data_13_1961.2]

/-- Complete interval computation for depth 13, residue 1962. -/
theorem bounds_13_1962 : exactInterval 13 1962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1962 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1962) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1962 : oddCount 1962 13 = 4 ∧ acceleratedOrbit 13 1962 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1962 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1962) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1962.1, data_13_1962.2]

/-- Complete interval computation for depth 13, residue 1963. -/
theorem bounds_13_1963 : exactInterval 13 1963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1963 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1963) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1963 : oddCount 1963 13 = 9 ∧ acceleratedOrbit 13 1963 = 4724 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1963 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1963) = 3 ^ 9 * m + 4724 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1963.1, data_13_1963.2]

/-- Complete interval computation for depth 13, residue 1964. -/
theorem bounds_13_1964 : exactInterval 13 1964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1964 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1964) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1964 : oddCount 1964 13 = 8 ∧ acceleratedOrbit 13 1964 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1964 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1964) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1964.1, data_13_1964.2]

/-- Complete interval computation for depth 13, residue 1965. -/
theorem bounds_13_1965 : exactInterval 13 1965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1965 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1965) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1965 : oddCount 1965 13 = 8 ∧ acceleratedOrbit 13 1965 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1965 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1965) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1965.1, data_13_1965.2]

/-- Complete interval computation for depth 13, residue 1966. -/
theorem bounds_13_1966 : exactInterval 13 1966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1966 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1966) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1966 : oddCount 1966 13 = 8 ∧ acceleratedOrbit 13 1966 = 1579 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1966 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1966) = 3 ^ 8 * m + 1579 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1966.1, data_13_1966.2]

/-- Complete interval computation for depth 13, residue 1967. -/
theorem bounds_13_1967 : exactInterval 13 1967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1967 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1967) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1967 : oddCount 1967 13 = 7 ∧ acceleratedOrbit 13 1967 = 526 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1967 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1967) = 3 ^ 7 * m + 526 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1967.1, data_13_1967.2]

/-- Complete interval computation for depth 13, residue 1968. -/
theorem bounds_13_1968 : exactInterval 13 1968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1968 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1968) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1968 : oddCount 1968 13 = 5 ∧ acceleratedOrbit 13 1968 = 59 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1968 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1968) = 3 ^ 5 * m + 59 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1968.1, data_13_1968.2]

/-- Complete interval computation for depth 13, residue 1969. -/
theorem bounds_13_1969 : exactInterval 13 1969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1969 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1969) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1969 : oddCount 1969 13 = 4 ∧ acceleratedOrbit 13 1969 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1969 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1969) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1969.1, data_13_1969.2]

/-- Complete interval computation for depth 13, residue 1970. -/
theorem bounds_13_1970 : exactInterval 13 1970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_1970 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 1970) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_1970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_1970 : oddCount 1970 13 = 4 ∧ acceleratedOrbit 13 1970 = 20 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_1970 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 1970) = 3 ^ 4 * m + 20 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_1970.1, data_13_1970.2]

end Collatz.Research.StoppingAtlas.Batch0595
