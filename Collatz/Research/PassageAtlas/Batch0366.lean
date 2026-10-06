import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.PassageAtlas.Batch0366

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 15, residue 11960. -/
theorem bounds_15_11960 : exactInterval 15 11960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11960 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11960) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11960 : oddCount 11960 15 = 7 ∧ acceleratedOrbit 15 11960 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11960 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11960) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11960.1, data_15_11960.2]

/-- Complete interval computation for depth 15, residue 11961. -/
theorem bounds_15_11961 : exactInterval 15 11961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11961 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11961) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11961 : oddCount 11961 15 = 8 ∧ acceleratedOrbit 15 11961 = 2396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11961 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11961) = 3 ^ 8 * m + 2396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11961.1, data_15_11961.2]

/-- Complete interval computation for depth 15, residue 11962. -/
theorem bounds_15_11962 : exactInterval 15 11962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11962 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11962) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11962 : oddCount 11962 15 = 7 ∧ acceleratedOrbit 15 11962 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11962 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11962) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11962.1, data_15_11962.2]

/-- Complete interval computation for depth 15, residue 11963. -/
theorem bounds_15_11963 : exactInterval 15 11963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11963 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11963) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11963 : oddCount 11963 15 = 8 ∧ acceleratedOrbit 15 11963 = 2396 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11963 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11963) = 3 ^ 8 * m + 2396 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11963.1, data_15_11963.2]

/-- Complete interval computation for depth 15, residue 11964. -/
theorem bounds_15_11964 : exactInterval 15 11964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11964 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11964) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11964 : oddCount 11964 15 = 7 ∧ acceleratedOrbit 15 11964 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11964 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11964) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11964.1, data_15_11964.2]

/-- Complete interval computation for depth 15, residue 11965. -/
theorem bounds_15_11965 : exactInterval 15 11965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11965 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11965) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11965 : oddCount 11965 15 = 7 ∧ acceleratedOrbit 15 11965 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11965 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11965) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11965.1, data_15_11965.2]

/-- Complete interval computation for depth 15, residue 11966. -/
theorem bounds_15_11966 : exactInterval 15 11966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11966 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11966) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11966 : oddCount 11966 15 = 7 ∧ acceleratedOrbit 15 11966 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11966 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11966) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11966.1, data_15_11966.2]

/-- Complete interval computation for depth 15, residue 11967. -/
theorem bounds_15_11967 : exactInterval 15 11967 = ⟨0, none⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11967 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11967) 15 ↔ 0 ≤ m := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11967 : oddCount 11967 15 = 9 ∧ acceleratedOrbit 15 11967 = 7189 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11967 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11967) = 3 ^ 9 * m + 7189 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11967.1, data_15_11967.2]

/-- Complete interval computation for depth 15, residue 11968. -/
theorem bounds_15_11968 : exactInterval 15 11968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11968 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11968) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11968 : oddCount 11968 15 = 6 ∧ acceleratedOrbit 15 11968 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11968 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11968) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11968.1, data_15_11968.2]

/-- Complete interval computation for depth 15, residue 11969. -/
theorem bounds_15_11969 : exactInterval 15 11969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11969 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11969) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11969 : oddCount 11969 15 = 7 ∧ acceleratedOrbit 15 11969 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11969 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11969) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11969.1, data_15_11969.2]

/-- Complete interval computation for depth 15, residue 11970. -/
theorem bounds_15_11970 : exactInterval 15 11970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11970 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11970) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11970 : oddCount 11970 15 = 8 ∧ acceleratedOrbit 15 11970 = 2398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11970 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11970) = 3 ^ 8 * m + 2398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11970.1, data_15_11970.2]

/-- Complete interval computation for depth 15, residue 11971. -/
theorem bounds_15_11971 : exactInterval 15 11971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11971 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11971) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11971 : oddCount 11971 15 = 8 ∧ acceleratedOrbit 15 11971 = 2398 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11971 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11971) = 3 ^ 8 * m + 2398 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11971.1, data_15_11971.2]

/-- Complete interval computation for depth 15, residue 11972. -/
theorem bounds_15_11972 : exactInterval 15 11972 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11972 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11972) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11972 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11972 : oddCount 11972 15 = 6 ∧ acceleratedOrbit 15 11972 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11972 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11972) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11972.1, data_15_11972.2]

/-- Complete interval computation for depth 15, residue 11973. -/
theorem bounds_15_11973 : exactInterval 15 11973 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11973 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11973) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11973 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11973 : oddCount 11973 15 = 6 ∧ acceleratedOrbit 15 11973 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11973 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11973) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11973.1, data_15_11973.2]

/-- Complete interval computation for depth 15, residue 11974. -/
theorem bounds_15_11974 : exactInterval 15 11974 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11974 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11974) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11974 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11974 : oddCount 11974 15 = 6 ∧ acceleratedOrbit 15 11974 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11974 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11974) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11974.1, data_15_11974.2]

/-- Complete interval computation for depth 15, residue 11975. -/
theorem bounds_15_11975 : exactInterval 15 11975 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11975 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11975) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11975 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11975 : oddCount 11975 15 = 7 ∧ acceleratedOrbit 15 11975 = 800 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11975 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11975) = 3 ^ 7 * m + 800 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11975.1, data_15_11975.2]

/-- Complete interval computation for depth 15, residue 11976. -/
theorem bounds_15_11976 : exactInterval 15 11976 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11976 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11976) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11976 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11976 : oddCount 11976 15 = 6 ∧ acceleratedOrbit 15 11976 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11976 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11976) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11976.1, data_15_11976.2]

/-- Complete interval computation for depth 15, residue 11977. -/
theorem bounds_15_11977 : exactInterval 15 11977 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11977 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11977) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11977 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11977 : oddCount 11977 15 = 9 ∧ acceleratedOrbit 15 11977 = 7199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11977 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11977) = 3 ^ 9 * m + 7199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11977.1, data_15_11977.2]

/-- Complete interval computation for depth 15, residue 11978. -/
theorem bounds_15_11978 : exactInterval 15 11978 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11978 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11978) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11978 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11978 : oddCount 11978 15 = 6 ∧ acceleratedOrbit 15 11978 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11978 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11978) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11978.1, data_15_11978.2]

/-- Complete interval computation for depth 15, residue 11979. -/
theorem bounds_15_11979 : exactInterval 15 11979 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11979 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11979) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11979 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11979 : oddCount 11979 15 = 9 ∧ acceleratedOrbit 15 11979 = 7199 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11979 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11979) = 3 ^ 9 * m + 7199 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11979.1, data_15_11979.2]

/-- Complete interval computation for depth 15, residue 11980. -/
theorem bounds_15_11980 : exactInterval 15 11980 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11980 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11980) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11980 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11980 : oddCount 11980 15 = 6 ∧ acceleratedOrbit 15 11980 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11980 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11980) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11980.1, data_15_11980.2]

/-- Complete interval computation for depth 15, residue 11981. -/
theorem bounds_15_11981 : exactInterval 15 11981 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11981 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11981) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11981 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11981 : oddCount 11981 15 = 6 ∧ acceleratedOrbit 15 11981 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11981 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11981) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11981.1, data_15_11981.2]

/-- Complete interval computation for depth 15, residue 11982. -/
theorem bounds_15_11982 : exactInterval 15 11982 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11982 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11982) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11982 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11982 : oddCount 11982 15 = 11 ∧ acceleratedOrbit 15 11982 = 64790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11982 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11982) = 3 ^ 11 * m + 64790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11982.1, data_15_11982.2]

/-- Complete interval computation for depth 15, residue 11983. -/
theorem bounds_15_11983 : exactInterval 15 11983 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11983 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11983) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11983 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11983 : oddCount 11983 15 = 11 ∧ acceleratedOrbit 15 11983 = 64790 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11983 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11983) = 3 ^ 11 * m + 64790 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11983.1, data_15_11983.2]

/-- Complete interval computation for depth 15, residue 11984. -/
theorem bounds_15_11984 : exactInterval 15 11984 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11984 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11984) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11984 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11984 : oddCount 11984 15 = 6 ∧ acceleratedOrbit 15 11984 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11984 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11984) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11984.1, data_15_11984.2]

/-- Complete interval computation for depth 15, residue 11985. -/
theorem bounds_15_11985 : exactInterval 15 11985 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11985 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11985) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11985 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11985 : oddCount 11985 15 = 8 ∧ acceleratedOrbit 15 11985 = 2402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11985 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11985) = 3 ^ 8 * m + 2402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11985.1, data_15_11985.2]

/-- Complete interval computation for depth 15, residue 11986. -/
theorem bounds_15_11986 : exactInterval 15 11986 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11986 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11986) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11986 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11986 : oddCount 11986 15 = 8 ∧ acceleratedOrbit 15 11986 = 2402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11986 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11986) = 3 ^ 8 * m + 2402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11986.1, data_15_11986.2]

/-- Complete interval computation for depth 15, residue 11987. -/
theorem bounds_15_11987 : exactInterval 15 11987 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11987 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11987) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11987 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11987 : oddCount 11987 15 = 8 ∧ acceleratedOrbit 15 11987 = 2402 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11987 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11987) = 3 ^ 8 * m + 2402 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11987.1, data_15_11987.2]

/-- Complete interval computation for depth 15, residue 11988. -/
theorem bounds_15_11988 : exactInterval 15 11988 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11988 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11988) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11988 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11988 : oddCount 11988 15 = 6 ∧ acceleratedOrbit 15 11988 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11988 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11988) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11988.1, data_15_11988.2]

/-- Complete interval computation for depth 15, residue 11989. -/
theorem bounds_15_11989 : exactInterval 15 11989 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11989 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11989) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11989 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11989 : oddCount 11989 15 = 6 ∧ acceleratedOrbit 15 11989 = 269 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11989 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11989) = 3 ^ 6 * m + 269 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11989.1, data_15_11989.2]

/-- Complete interval computation for depth 15, residue 11990. -/
theorem bounds_15_11990 : exactInterval 15 11990 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11990 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11990) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11990 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11990 : oddCount 11990 15 = 9 ∧ acceleratedOrbit 15 11990 = 7208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11990 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11990) = 3 ^ 9 * m + 7208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11990.1, data_15_11990.2]

/-- Complete interval computation for depth 15, residue 11991. -/
theorem bounds_15_11991 : exactInterval 15 11991 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11991 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11991) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11991 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11991 : oddCount 11991 15 = 9 ∧ acceleratedOrbit 15 11991 = 7208 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11991 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11991) = 3 ^ 9 * m + 7208 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11991.1, data_15_11991.2]

/-- Complete interval computation for depth 15, residue 11992. -/
theorem bounds_15_11992 : exactInterval 15 11992 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_15_11992 (m : Nat) :
    stoppingTime (2 ^ 15 * m + 11992) 15 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_15_11992 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_15_11992 : oddCount 11992 15 = 5 ∧ acceleratedOrbit 15 11992 = 89 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_15_11992 (m : Nat) :
    acceleratedOrbit 15 (2 ^ 15 * m + 11992) = 3 ^ 5 * m + 89 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_15_11992.1, data_15_11992.2]

end Collatz.Research.PassageAtlas.Batch0366
