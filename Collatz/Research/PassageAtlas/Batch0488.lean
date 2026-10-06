import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0488

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 15958. -/
theorem bounds_15_15958 : exactInterval 15 15958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15958 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15958) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15958 : oddCount 15958 15 = 7 ∧ acceleratedOrbit 15 15958 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15958 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15958) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15958.1, data_15_15958.2]

/-- Complete interval computation for depth 15, residue 15959. -/
theorem bounds_15_15959 : exactInterval 15 15959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15959 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15959) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15959 : oddCount 15959 15 = 7 ∧ acceleratedOrbit 15 15959 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15959 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15959) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15959.1, data_15_15959.2]

/-- Complete interval computation for depth 15, residue 15960. -/
theorem bounds_15_15960 : exactInterval 15 15960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15960 : oddCount 15960 15 = 5 ∧ acceleratedOrbit 15 15960 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15960) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15960.1, data_15_15960.2]

/-- Complete interval computation for depth 15, residue 15961. -/
theorem bounds_15_15961 : exactInterval 15 15961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15961 : oddCount 15961 15 = 8 ∧ acceleratedOrbit 15 15961 = 3197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15961) = 3 ^ 8 * m + 3197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15961.1, data_15_15961.2]

/-- Complete interval computation for depth 15, residue 15962. -/
theorem bounds_15_15962 : exactInterval 15 15962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15962 : oddCount 15962 15 = 5 ∧ acceleratedOrbit 15 15962 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15962) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15962.1, data_15_15962.2]

/-- Complete interval computation for depth 15, residue 15963. -/
theorem bounds_15_15963 : exactInterval 15 15963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15963 : oddCount 15963 15 = 8 ∧ acceleratedOrbit 15 15963 = 3197 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15963) = 3 ^ 8 * m + 3197 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15963.1, data_15_15963.2]

/-- Complete interval computation for depth 15, residue 15964. -/
theorem bounds_15_15964 : exactInterval 15 15964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15964 : oddCount 15964 15 = 5 ∧ acceleratedOrbit 15 15964 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15964) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15964.1, data_15_15964.2]

/-- Complete interval computation for depth 15, residue 15965. -/
theorem bounds_15_15965 : exactInterval 15 15965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15965 : oddCount 15965 15 = 5 ∧ acceleratedOrbit 15 15965 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15965) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15965.1, data_15_15965.2]

/-- Complete interval computation for depth 15, residue 15966. -/
theorem bounds_15_15966 : exactInterval 15 15966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15966 : oddCount 15966 15 = 7 ∧ acceleratedOrbit 15 15966 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15966) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15966.1, data_15_15966.2]

/-- Complete interval computation for depth 15, residue 15967. -/
theorem bounds_15_15967 : exactInterval 15 15967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15967) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15967 : oddCount 15967 15 = 7 ∧ acceleratedOrbit 15 15967 = 1066 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15967) = 3 ^ 7 * m + 1066 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15967.1, data_15_15967.2]

/-- Complete interval computation for depth 15, residue 15968. -/
theorem bounds_15_15968 : exactInterval 15 15968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15968 : oddCount 15968 15 = 5 ∧ acceleratedOrbit 15 15968 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15968) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15968.1, data_15_15968.2]

/-- Complete interval computation for depth 15, residue 15969. -/
theorem bounds_15_15969 : exactInterval 15 15969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15969 : oddCount 15969 15 = 8 ∧ acceleratedOrbit 15 15969 = 3199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15969) = 3 ^ 8 * m + 3199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15969.1, data_15_15969.2]

/-- Complete interval computation for depth 15, residue 15970. -/
theorem bounds_15_15970 : exactInterval 15 15970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15970 : oddCount 15970 15 = 5 ∧ acceleratedOrbit 15 15970 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15970) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15970.1, data_15_15970.2]

/-- Complete interval computation for depth 15, residue 15971. -/
theorem bounds_15_15971 : exactInterval 15 15971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15971 : oddCount 15971 15 = 5 ∧ acceleratedOrbit 15 15971 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15971) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15971.1, data_15_15971.2]

/-- Complete interval computation for depth 15, residue 15972. -/
theorem bounds_15_15972 : exactInterval 15 15972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15972 : oddCount 15972 15 = 5 ∧ acceleratedOrbit 15 15972 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15972) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15972.1, data_15_15972.2]

/-- Complete interval computation for depth 15, residue 15973. -/
theorem bounds_15_15973 : exactInterval 15 15973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15973 : oddCount 15973 15 = 5 ∧ acceleratedOrbit 15 15973 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15973) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15973.1, data_15_15973.2]

/-- Complete interval computation for depth 15, residue 15974. -/
theorem bounds_15_15974 : exactInterval 15 15974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15974 : oddCount 15974 15 = 5 ∧ acceleratedOrbit 15 15974 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15974) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15974.1, data_15_15974.2]

/-- Complete interval computation for depth 15, residue 15975. -/
theorem bounds_15_15975 : exactInterval 15 15975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15975 : oddCount 15975 15 = 11 ∧ acceleratedOrbit 15 15975 = 86372 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15975) = 3 ^ 11 * m + 86372 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15975.1, data_15_15975.2]

/-- Complete interval computation for depth 15, residue 15976. -/
theorem bounds_15_15976 : exactInterval 15 15976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15976 : oddCount 15976 15 = 5 ∧ acceleratedOrbit 15 15976 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15976) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15976.1, data_15_15976.2]

/-- Complete interval computation for depth 15, residue 15977. -/
theorem bounds_15_15977 : exactInterval 15 15977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15977 : oddCount 15977 15 = 11 ∧ acceleratedOrbit 15 15977 = 86386 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15977) = 3 ^ 11 * m + 86386 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15977.1, data_15_15977.2]

/-- Complete interval computation for depth 15, residue 15978. -/
theorem bounds_15_15978 : exactInterval 15 15978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15978 : oddCount 15978 15 = 5 ∧ acceleratedOrbit 15 15978 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15978) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15978.1, data_15_15978.2]

/-- Complete interval computation for depth 15, residue 15979. -/
theorem bounds_15_15979 : exactInterval 15 15979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15979 : oddCount 15979 15 = 8 ∧ acceleratedOrbit 15 15979 = 3200 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15979) = 3 ^ 8 * m + 3200 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15979.1, data_15_15979.2]

/-- Complete interval computation for depth 15, residue 15980. -/
theorem bounds_15_15980 : exactInterval 15 15980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15980 : oddCount 15980 15 = 7 ∧ acceleratedOrbit 15 15980 = 1067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15980) = 3 ^ 7 * m + 1067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15980.1, data_15_15980.2]

/-- Complete interval computation for depth 15, residue 15981. -/
theorem bounds_15_15981 : exactInterval 15 15981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15981 : oddCount 15981 15 = 7 ∧ acceleratedOrbit 15 15981 = 1067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15981) = 3 ^ 7 * m + 1067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15981.1, data_15_15981.2]

/-- Complete interval computation for depth 15, residue 15982. -/
theorem bounds_15_15982 : exactInterval 15 15982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15982 : oddCount 15982 15 = 7 ∧ acceleratedOrbit 15 15982 = 1067 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15982) = 3 ^ 7 * m + 1067 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15982.1, data_15_15982.2]

/-- Complete interval computation for depth 15, residue 15983. -/
theorem bounds_15_15983 : exactInterval 15 15983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15983 : oddCount 15983 15 = 9 ∧ acceleratedOrbit 15 15983 = 9602 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15983) = 3 ^ 9 * m + 9602 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15983.1, data_15_15983.2]

/-- Complete interval computation for depth 15, residue 15984. -/
theorem bounds_15_15984 : exactInterval 15 15984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15984 : oddCount 15984 15 = 6 ∧ acceleratedOrbit 15 15984 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15984) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15984.1, data_15_15984.2]

/-- Complete interval computation for depth 15, residue 15985. -/
theorem bounds_15_15985 : exactInterval 15 15985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15985 : oddCount 15985 15 = 5 ∧ acceleratedOrbit 15 15985 = 119 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15985) = 3 ^ 5 * m + 119 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15985.1, data_15_15985.2]

/-- Complete interval computation for depth 15, residue 15986. -/
theorem bounds_15_15986 : exactInterval 15 15986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15986 : oddCount 15986 15 = 8 ∧ acceleratedOrbit 15 15986 = 3203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15986) = 3 ^ 8 * m + 3203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15986.1, data_15_15986.2]

/-- Complete interval computation for depth 15, residue 15987. -/
theorem bounds_15_15987 : exactInterval 15 15987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15987 : oddCount 15987 15 = 8 ∧ acceleratedOrbit 15 15987 = 3203 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15987) = 3 ^ 8 * m + 3203 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15987.1, data_15_15987.2]

/-- Complete interval computation for depth 15, residue 15988. -/
theorem bounds_15_15988 : exactInterval 15 15988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15988 : oddCount 15988 15 = 6 ∧ acceleratedOrbit 15 15988 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15988) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15988.1, data_15_15988.2]

/-- Complete interval computation for depth 15, residue 15989. -/
theorem bounds_15_15989 : exactInterval 15 15989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_15989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 15989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_15989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_15989 : oddCount 15989 15 = 6 ∧ acceleratedOrbit 15 15989 = 356 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_15989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 15989) = 3 ^ 6 * m + 356 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_15989.1, data_15_15989.2]

end Collatz.Research.PassageAtlas.Batch0488
