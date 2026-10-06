import Collatz.Research.DescentIntervals.Classifier

namespace Collatz.Research.StoppingAtlas.Batch0530

open Collatz.Research.DescentIntervals

set_option maxRecDepth 20000
set_option maxHeartbeats 0

/-- Complete interval computation for depth 13, residue 957. -/
theorem bounds_13_957 : exactInterval 13 957 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_957 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 957) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_957 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_957 : oddCount 957 13 = 9 ∧ acceleratedOrbit 13 957 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_957 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 957) = 3 ^ 9 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_957.1, data_13_957.2]

/-- Complete interval computation for depth 13, residue 958. -/
theorem bounds_13_958 : exactInterval 13 958 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_958 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 958) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_958 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_958 : oddCount 958 13 = 9 ∧ acceleratedOrbit 13 958 = 2308 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_958 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 958) = 3 ^ 9 * m + 2308 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_958.1, data_13_958.2]

/-- Complete interval computation for depth 13, residue 959. -/
theorem bounds_13_959 : exactInterval 13 959 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_959 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 959) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_959 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_959 : oddCount 959 13 = 11 ∧ acceleratedOrbit 13 959 = 20762 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_959 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 959) = 3 ^ 11 * m + 20762 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_959.1, data_13_959.2]

/-- Complete interval computation for depth 13, residue 960. -/
theorem bounds_13_960 : exactInterval 13 960 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_960 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 960) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_960 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_960 : oddCount 960 13 = 4 ∧ acceleratedOrbit 13 960 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_960 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 960) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_960.1, data_13_960.2]

/-- Complete interval computation for depth 13, residue 961. -/
theorem bounds_13_961 : exactInterval 13 961 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_961 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 961) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_961 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_961 : oddCount 961 13 = 6 ∧ acceleratedOrbit 13 961 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_961 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 961) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_961.1, data_13_961.2]

/-- Complete interval computation for depth 13, residue 962. -/
theorem bounds_13_962 : exactInterval 13 962 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_962 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 962) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_962 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_962 : oddCount 962 13 = 6 ∧ acceleratedOrbit 13 962 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_962 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 962) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_962.1, data_13_962.2]

/-- Complete interval computation for depth 13, residue 963. -/
theorem bounds_13_963 : exactInterval 13 963 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_963 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 963) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_963 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_963 : oddCount 963 13 = 6 ∧ acceleratedOrbit 13 963 = 86 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_963 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 963) = 3 ^ 6 * m + 86 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_963.1, data_13_963.2]

/-- Complete interval computation for depth 13, residue 964. -/
theorem bounds_13_964 : exactInterval 13 964 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_964 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 964) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_964 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_964 : oddCount 964 13 = 4 ∧ acceleratedOrbit 13 964 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_964 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 964) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_964.1, data_13_964.2]

/-- Complete interval computation for depth 13, residue 965. -/
theorem bounds_13_965 : exactInterval 13 965 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_965 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 965) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_965 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_965 : oddCount 965 13 = 4 ∧ acceleratedOrbit 13 965 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_965 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 965) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_965.1, data_13_965.2]

/-- Complete interval computation for depth 13, residue 966. -/
theorem bounds_13_966 : exactInterval 13 966 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_966 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 966) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_966 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_966 : oddCount 966 13 = 4 ∧ acceleratedOrbit 13 966 = 10 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_966 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 966) = 3 ^ 4 * m + 10 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_966.1, data_13_966.2]

/-- Complete interval computation for depth 13, residue 967. -/
theorem bounds_13_967 : exactInterval 13 967 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_967 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 967) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_967 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_967 : oddCount 967 13 = 8 ∧ acceleratedOrbit 13 967 = 776 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_967 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 967) = 3 ^ 8 * m + 776 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_967.1, data_13_967.2]

/-- Complete interval computation for depth 13, residue 968. -/
theorem bounds_13_968 : exactInterval 13 968 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_968 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 968) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_968 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_968 : oddCount 968 13 = 7 ∧ acceleratedOrbit 13 968 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_968 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 968) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_968.1, data_13_968.2]

/-- Complete interval computation for depth 13, residue 969. -/
theorem bounds_13_969 : exactInterval 13 969 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_969 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 969) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_969 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_969 : oddCount 969 13 = 7 ∧ acceleratedOrbit 13 969 = 260 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_969 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 969) = 3 ^ 7 * m + 260 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_969.1, data_13_969.2]

/-- Complete interval computation for depth 13, residue 970. -/
theorem bounds_13_970 : exactInterval 13 970 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_970 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 970) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_970 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_970 : oddCount 970 13 = 7 ∧ acceleratedOrbit 13 970 = 263 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_970 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 970) = 3 ^ 7 * m + 263 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_970.1, data_13_970.2]

/-- Complete interval computation for depth 13, residue 971. -/
theorem bounds_13_971 : exactInterval 13 971 = ⟨0, some 0⟩ := by
  decide

/-- Exact classification for every natural class index, not a finite sample. -/
theorem exact_13_971 (m : Nat) :
    stoppingTime (2 ^ 13 * m + 971) 13 ↔ 0 ≤ m ∧ m < 0 := by
  simpa only [IndexInterval.Contains, and_true] using
    exact_of_certificate bounds_13_971 m

/-- Independently checked base parity and endpoint arithmetic. -/
theorem data_13_971 : oddCount 971 13 = 5 ∧ acceleratedOrbit 13 971 = 29 := by
  decide

/-- Symbolic endpoint for the entire infinite dyadic class. -/
theorem endpoint_13_971 (m : Nat) :
    acceleratedOrbit 13 (2 ^ 13 * m + 971) = 3 ^ 5 * m + 29 := by
  rw [Congruence.accOrbit_pow_two_mul_add, data_13_971.1, data_13_971.2]

end Collatz.Research.StoppingAtlas.Batch0530
