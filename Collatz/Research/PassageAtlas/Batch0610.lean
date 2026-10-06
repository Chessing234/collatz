import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0610

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 19955. -/
theorem bounds_15_19955 : exactInterval 15 19955 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19955 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19955) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19955 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19955 : oddCount 19955 15 = 5 ∧ acceleratedOrbit 15 19955 = 148 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19955 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19955) = 3 ^ 5 * m + 148 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19955.1, data_15_19955.2]

/-- Complete interval computation for depth 15, residue 19956. -/
theorem bounds_15_19956 : exactInterval 15 19956 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19956 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19956) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19956 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19956 : oddCount 19956 15 = 7 ∧ acceleratedOrbit 15 19956 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19956 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19956) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19956.1, data_15_19956.2]

/-- Complete interval computation for depth 15, residue 19957. -/
theorem bounds_15_19957 : exactInterval 15 19957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19957 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19957) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19957 : oddCount 19957 15 = 7 ∧ acceleratedOrbit 15 19957 = 1333 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19957 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19957) = 3 ^ 7 * m + 1333 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19957.1, data_15_19957.2]

/-- Complete interval computation for depth 15, residue 19958. -/
theorem bounds_15_19958 : exactInterval 15 19958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19958 : oddCount 19958 15 = 8 ∧ acceleratedOrbit 15 19958 = 3997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19958) = 3 ^ 8 * m + 3997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19958.1, data_15_19958.2]

/-- Complete interval computation for depth 15, residue 19959. -/
theorem bounds_15_19959 : exactInterval 15 19959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19959 : oddCount 19959 15 = 8 ∧ acceleratedOrbit 15 19959 = 3997 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19959) = 3 ^ 8 * m + 3997 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19959.1, data_15_19959.2]

/-- Complete interval computation for depth 15, residue 19960. -/
theorem bounds_15_19960 : exactInterval 15 19960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19960 : oddCount 19960 15 = 10 ∧ acceleratedOrbit 15 19960 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19960) = 3 ^ 10 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19960.1, data_15_19960.2]

/-- Complete interval computation for depth 15, residue 19961. -/
theorem bounds_15_19961 : exactInterval 15 19961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19961 : oddCount 19961 15 = 8 ∧ acceleratedOrbit 15 19961 = 3998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19961) = 3 ^ 8 * m + 3998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19961.1, data_15_19961.2]

/-- Complete interval computation for depth 15, residue 19962. -/
theorem bounds_15_19962 : exactInterval 15 19962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19962 : oddCount 19962 15 = 10 ∧ acceleratedOrbit 15 19962 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19962) = 3 ^ 10 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19962.1, data_15_19962.2]

/-- Complete interval computation for depth 15, residue 19963. -/
theorem bounds_15_19963 : exactInterval 15 19963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19963 : oddCount 19963 15 = 8 ∧ acceleratedOrbit 15 19963 = 3998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19963) = 3 ^ 8 * m + 3998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19963.1, data_15_19963.2]

/-- Complete interval computation for depth 15, residue 19964. -/
theorem bounds_15_19964 : exactInterval 15 19964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19964 : oddCount 19964 15 = 10 ∧ acceleratedOrbit 15 19964 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19964) = 3 ^ 10 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19964.1, data_15_19964.2]

/-- Complete interval computation for depth 15, residue 19965. -/
theorem bounds_15_19965 : exactInterval 15 19965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19965 : oddCount 19965 15 = 10 ∧ acceleratedOrbit 15 19965 = 35984 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19965) = 3 ^ 10 * m + 35984 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19965.1, data_15_19965.2]

/-- Complete interval computation for depth 15, residue 19966. -/
theorem bounds_15_19966 : exactInterval 15 19966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19966 : oddCount 19966 15 = 10 ∧ acceleratedOrbit 15 19966 = 35983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19966) = 3 ^ 10 * m + 35983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19966.1, data_15_19966.2]

/-- Complete interval computation for depth 15, residue 19967. -/
theorem bounds_15_19967 : exactInterval 15 19967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19967 : oddCount 19967 15 = 10 ∧ acceleratedOrbit 15 19967 = 35983 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19967) = 3 ^ 10 * m + 35983 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19967.1, data_15_19967.2]

/-- Complete interval computation for depth 15, residue 19968. -/
theorem bounds_15_19968 : exactInterval 15 19968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19968 : oddCount 19968 15 = 5 ∧ acceleratedOrbit 15 19968 = 152 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19968) = 3 ^ 5 * m + 152 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19968.1, data_15_19968.2]

/-- Complete interval computation for depth 15, residue 19969. -/
theorem bounds_15_19969 : exactInterval 15 19969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19969 : oddCount 19969 15 = 9 ∧ acceleratedOrbit 15 19969 = 11998 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19969) = 3 ^ 9 * m + 11998 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19969.1, data_15_19969.2]

/-- Complete interval computation for depth 15, residue 19970. -/
theorem bounds_15_19970 : exactInterval 15 19970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19970 : oddCount 19970 15 = 6 ∧ acceleratedOrbit 15 19970 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19970) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19970.1, data_15_19970.2]

/-- Complete interval computation for depth 15, residue 19971. -/
theorem bounds_15_19971 : exactInterval 15 19971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19971 : oddCount 19971 15 = 6 ∧ acceleratedOrbit 15 19971 = 445 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19971) = 3 ^ 6 * m + 445 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19971.1, data_15_19971.2]

/-- Complete interval computation for depth 15, residue 19972. -/
theorem bounds_15_19972 : exactInterval 15 19972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19972 : oddCount 19972 15 = 7 ∧ acceleratedOrbit 15 19972 = 1334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19972) = 3 ^ 7 * m + 1334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19972.1, data_15_19972.2]

/-- Complete interval computation for depth 15, residue 19973. -/
theorem bounds_15_19973 : exactInterval 15 19973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19973 : oddCount 19973 15 = 7 ∧ acceleratedOrbit 15 19973 = 1334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19973) = 3 ^ 7 * m + 1334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19973.1, data_15_19973.2]

/-- Complete interval computation for depth 15, residue 19974. -/
theorem bounds_15_19974 : exactInterval 15 19974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19974 : oddCount 19974 15 = 7 ∧ acceleratedOrbit 15 19974 = 1334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19974) = 3 ^ 7 * m + 1334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19974.1, data_15_19974.2]

/-- Complete interval computation for depth 15, residue 19975. -/
theorem bounds_15_19975 : exactInterval 15 19975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19975 : oddCount 19975 15 = 9 ∧ acceleratedOrbit 15 19975 = 12001 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19975) = 3 ^ 9 * m + 12001 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19975.1, data_15_19975.2]

/-- Complete interval computation for depth 15, residue 19976. -/
theorem bounds_15_19976 : exactInterval 15 19976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19976 : oddCount 19976 15 = 7 ∧ acceleratedOrbit 15 19976 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19976) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19976.1, data_15_19976.2]

/-- Complete interval computation for depth 15, residue 19977. -/
theorem bounds_15_19977 : exactInterval 15 19977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19977 : oddCount 19977 15 = 7 ∧ acceleratedOrbit 15 19977 = 1334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19977) = 3 ^ 7 * m + 1334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19977.1, data_15_19977.2]

/-- Complete interval computation for depth 15, residue 19978. -/
theorem bounds_15_19978 : exactInterval 15 19978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19978 : oddCount 19978 15 = 7 ∧ acceleratedOrbit 15 19978 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19978) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19978.1, data_15_19978.2]

/-- Complete interval computation for depth 15, residue 19979. -/
theorem bounds_15_19979 : exactInterval 15 19979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19979 : oddCount 19979 15 = 7 ∧ acceleratedOrbit 15 19979 = 1334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19979) = 3 ^ 7 * m + 1334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19979.1, data_15_19979.2]

/-- Complete interval computation for depth 15, residue 19980. -/
theorem bounds_15_19980 : exactInterval 15 19980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19980 : oddCount 19980 15 = 7 ∧ acceleratedOrbit 15 19980 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19980) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19980.1, data_15_19980.2]

/-- Complete interval computation for depth 15, residue 19981. -/
theorem bounds_15_19981 : exactInterval 15 19981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19981 : oddCount 19981 15 = 7 ∧ acceleratedOrbit 15 19981 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19981) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19981.1, data_15_19981.2]

/-- Complete interval computation for depth 15, residue 19982. -/
theorem bounds_15_19982 : exactInterval 15 19982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19982 : oddCount 19982 15 = 7 ∧ acceleratedOrbit 15 19982 = 1334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19982) = 3 ^ 7 * m + 1334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19982.1, data_15_19982.2]

/-- Complete interval computation for depth 15, residue 19983. -/
theorem bounds_15_19983 : exactInterval 15 19983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19983 : oddCount 19983 15 = 7 ∧ acceleratedOrbit 15 19983 = 1334 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19983) = 3 ^ 7 * m + 1334 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19983.1, data_15_19983.2]

/-- Complete interval computation for depth 15, residue 19984. -/
theorem bounds_15_19984 : exactInterval 15 19984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19984 : oddCount 19984 15 = 8 ∧ acceleratedOrbit 15 19984 = 4009 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19984) = 3 ^ 8 * m + 4009 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19984.1, data_15_19984.2]

/-- Complete interval computation for depth 15, residue 19985. -/
theorem bounds_15_19985 : exactInterval 15 19985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19985 : oddCount 19985 15 = 7 ∧ acceleratedOrbit 15 19985 = 1336 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19985) = 3 ^ 7 * m + 1336 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19985.1, data_15_19985.2]

/-- Complete interval computation for depth 15, residue 19986. -/
theorem bounds_15_19986 : exactInterval 15 19986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19986 : oddCount 19986 15 = 9 ∧ acceleratedOrbit 15 19986 = 12008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19986) = 3 ^ 9 * m + 12008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19986.1, data_15_19986.2]

/-- Complete interval computation for depth 15, residue 19987. -/
theorem bounds_15_19987 : exactInterval 15 19987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_19987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 19987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_19987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_19987 : oddCount 19987 15 = 9 ∧ acceleratedOrbit 15 19987 = 12008 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_19987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 19987) = 3 ^ 9 * m + 12008 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_19987.1, data_15_19987.2]

end Collatz.Research.PassageAtlas.Batch0610
